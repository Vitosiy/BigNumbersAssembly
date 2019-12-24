.model flat, stdcall
option casemap:none

includelib msvcrtd
includelib oldnames
includelib legacy_stdio_definitions.lib

printf proto c :dword, :vararg
malloc proto c :dword
calloc proto c :dword, :dword
realloc proto c :dword, :dword
memcpy proto c :dword, :dword, :dword
free proto c :dword

number struct
	nlen		dd ? ;len of number (31482168 12358732 123517239) -> 3
	nptr		dd ? ;ptr to mass of numbers (has to be called like invoke malloc, 100; mov eax, nptr
	sign		byte ? ;if number < 0 sign is set to 1
number ends

.data

.data?

.const
minus db "-", 0
fHex db "%08x", 0
newline db " ", 13, 10, 0
zeros db "00000000", 0
and_ db "&:", 0
or_ db "|:", 0
xor_ db "^:", 0
add_ db "+:", 0
sub_ db "-:", 0
mul_ db "*:", 0
mul__ db "**:", 0

er_wrong_argc db "Wrong arguments number! Please, specify following: number1 number2", 13, 10, 0
er_wrong_arg db "Wrong argument!", 13, 10, 0
.code

nAdd proto stdcall :ptr number, :ptr number, :ptr number

;-----------------------------------ADDTIONAL FUNCTIONS-----------------------------------
strlen proc uses edi ebx sPtr:dword
	local cntr:dword
	mov [cntr], 0
	mov edi, [sPtr]

	.while 1
		mov bl, byte ptr [edi]
		inc	[cntr]
		inc edi
		.if bl == 0
			mov eax, [cntr]
			dec eax
			ret
		.endif
	.endw
strlen endp

isStringValid proc uses esi sPtr:dword
	local weHaveMinus:byte
	mov al, 1
	cld 
	mov esi, [sPtr]
	lodsb
	.if al == '-' 
		mov [weHaveMinus], 1
	.elseif al >= '0' && al <= '9' || al >= 'a' || al <= 'f'
		mov [weHaveMinus], 0
	.else
		mov eax, 0
		ret
	.endif

	invoke strlen, [sPtr]
	.if [weHaveMinus] == 1 && eax == 1
		mov eax, 0
		ret
	.endif

	.while 1
		lodsb
		.if al == 0
			mov eax, 1
			ret
		.endif
		.if al < '0' || al > '9' && al < 'a' || al > 'f'
			mov eax, 0
			ret
		.endif
	.endw
	
	mov eax, 1
	ret
isStringValid endp

atoiSizeHex proc uses ecx esi edx sPtr:dword, sz:dword
	mov esi, [sPtr]
	mov ecx, [sz]

	cld ;up in mem
    xor edx, edx
    xor eax, eax

counter:
    imul edx, 10h            ;mul by 10h
    lodsb
	.if al >= '0' && al <= '9'
		sub al, 30h
	.else
		sub al, 57h
	.endif
    add edx, eax            ;add new num

    loop [counter]

    mov eax, edx
	ret
atoiSizeHex endp

;		| 1, n1 > n2	
; res = | 0 n1 == n2				(w/o signs)
;		| -1, n1 < n2
nCmp proc uses ebx ecx esi edi n1:ptr number, n2:ptr number
	local len1:dword
	local len2:dword
	local maxLen:dword
	local n1p:dword
	local n2p:dword

	mov eax, [n1]
	mov ecx, [eax].number.nlen
	mov [len1], ecx
	mov eax, [n2]
	mov ecx, [eax].number.nlen
	mov [len2], ecx
	
	mov eax, [len1]
	.if eax > [len2]
		mov eax, 1
		ret
	.elseif eax < [len2]
		mov eax, -1
		ret
	.endif
	mov [maxLen], eax

	;load ptrs and move them to the highest numbers
	mov eax, [n1]
	mov eax, [eax].number.nptr
	mov [n1p], eax
	mov ebx, 4

	mov eax, [n1]
	mov eax, [eax].number.nlen
	mul ebx
	add [n1p], eax
	sub [n1p], 4

	mov eax, [n2]
	mov eax, [eax].number.nptr
	mov [n2p], eax
	mov ebx, 4

	mov eax, [n2]
	mov eax, [eax].number.nlen
	mul ebx
	add [n2p], eax
	sub [n2p], 4

	.while [maxLen] != 0
		mov eax, dword ptr [n1p]
		mov esi, [eax]

		mov ebx, dword ptr [n2p]
		mov edi, [ebx]

		.if esi > edi
			mov eax, 1
			ret
		.endif
		.if esi < edi
			mov eax, -1
			ret
		.endif

		mov ecx, 4
		sub [n1p], ecx
		sub [n2p], ecx
		dec [maxLen]
	.endw

	mov eax, 0
	ret
nCmp endp

nShl proc uses eax ebx ecx edx p:ptr number
	local oldSizeBytes:dword

	mov eax, [p]
	inc [eax].number.nlen
	mov eax, [eax].number.nlen
	mov ebx, 4
	mul ebx
	mov [oldSizeBytes], eax
	sub [oldSizeBytes], 4
	mov ebx, [p]
	mov ebx, [ebx].number.nptr
	
	invoke realloc, ebx, eax
	mov ebx, eax
	add ebx, 4
	invoke memcpy, ebx, eax, [oldSizeBytes]
	mov ebx, [p]
	sub eax, 4
	mov [ebx].number.nptr, eax
	mov dword ptr [eax], 0 

	ret
nShl endp

;-----------------------------------BASE FUNCTIONALITY-----------------------------------
nInitByInt proc uses eax ebx p:ptr number, num:dword
	invoke calloc, 4, 1
	mov ecx, [num]
	mov dword ptr [eax], ecx
	mov ebx, [p]
	mov [ebx].number.nptr, eax
	mov [ebx].number.nlen, 1
	mov [ebx].number.sign, 0

	ret
nInitByInt endp

nInitByPosStringHex proc uses ebx ecx edx edi esi p:ptr number, pStr:dword
	local cntr:dword
	local aligned:byte 

	invoke strlen, [pStr]
	mov [cntr], eax
	mov ecx, 8
	xor edx, edx
	div ecx ; edx:eax / ecx(4) -> eax = res; this is about getting len of num in blocks

	.if edx != 0 ; 10 / 4 -> 2, but we have another extra 2 bytes, so inc
		inc eax
		mov [aligned], 0
	.else
		mov [aligned], 1
	.endif

	mov ebx, [p]
	mov [ebx].number.nlen, eax
	mov [ebx].number.sign, 0

	pushad
	invoke calloc, eax, 4
	mov [ebx].number.nptr, eax
	popad

	;going up in mem until we hit the 0
	xor ecx, ecx
	mov esi, [pStr]
	add esi, [cntr]
	mov dl, 100
	.while dl != 0
		inc ecx
		dec esi
		mov dl, byte ptr [esi]
		.if ecx == 8 && dl != 0
			invoke atoiSizeHex, esi, 8
			mov edi, [p]
			mov edi, [edi].number.nptr
			mov [edi], eax
			add [ebx].number.nptr, 4
			mov ecx, 0
		.endif
	.endw
	dec ecx

	.if ecx != 0
		inc esi
		invoke atoiSizeHex, esi, ecx
		mov edi, [p]
		mov edi, [edi].number.nptr
		mov [edi], eax
	.endif
	
	;mov ptr to the beg. of the num: 1234567890 -> 34567890 12 -> ptr will point at 34567890
	mov ebx, [p]
	mov eax, [ebx].number.nlen
	dec eax
	mov ebx, 4
	mul ebx
	mov ecx, [p]
	mov ecx, [ecx].number.nptr
	.if [aligned] == 1
		sub ecx, 4
	.endif
	sub ecx, eax
	mov ebx, [p]
	mov [ebx].number.nptr, ecx

	ret
nInitByPosStringHex endp

nInitByNegStringHex proc uses ebx ecx edx edi esi p:ptr number, pStr:dword
	local cntr:dword
	local aligned:byte 

	invoke strlen, [pStr]
	mov [cntr], eax
	mov ecx, 8
	xor edx, edx
	div ecx ; edx:eax / ecx(4) -> eax = res; this is about getting len of num in blocks

	.if edx != 0 ; 10 / 4 -> 2, but we have another extra 2 bytes, so inc
		mov [aligned], 0
		inc eax
	.else
		mov [aligned], 1
	.endif

	mov ebx, [p]
	mov [ebx].number.nlen, eax
	mov [ebx].number.sign, 1 ;it is the only diff

	pushad
	invoke calloc, eax, 4
	mov [ebx].number.nptr, eax
	popad

	;going up in mem until we hit the 0
	xor ecx, ecx
	mov esi, [pStr]
	add esi, [cntr]
	mov dl, 100
	.while dl != 45
		inc ecx
		dec esi
		mov dl, byte ptr [esi]
		.if ecx == 8 && dl != 45
			invoke atoiSizeHex, esi, 8
			mov edi, [p]
			mov edi, [edi].number.nptr
			mov [edi], eax
			add [ebx].number.nptr, 4
			mov ecx, 0
		.endif
	.endw
	dec ecx

	.if ecx != 0
		inc esi
		invoke atoiSizeHex, esi, ecx
		mov edi, [p]
		mov edi, [edi].number.nptr
		mov [edi], eax
	.endif
	
	;mov ptr to the beg. of the num: 1234567890 -> 34567890 12 -> ptr will point at 34567890
	mov ebx, [p]
	mov eax, [ebx].number.nlen
	dec eax
	mov ebx, 4
	mul ebx
	mov ecx, [p]
	mov ecx, [ecx].number.nptr
	.if [aligned] == 1
		sub ecx, 4
	.endif
	sub ecx, eax
	mov ebx, [p]
	mov [ebx].number.nptr, ecx

	ret
nInitByNegStringHex endp

nInitByStringHex proc uses ebx p:ptr number, pStr:dword
	local negInt:byte
	mov eax, [pStr]
	mov bl, byte ptr [eax]
	.if bl == '-'
		mov [negInt], 1
	.else
		mov [negInt], 0
	.endif

	.if [negInt] == 1
		inc [pStr]
		invoke nInitByNegStringHex, [p], [pStr]
	.else
		invoke nInitByPosStringHex, [p], [pStr]
	.endif
	
	mov eax, p
	ret		
nInitByStringHex endp

nSub proc uses eax ebx ecx edx edi esi n1:ptr number, n2:ptr number, res:ptr number
	local n1isNeg:byte
	local n2isNeg:byte
	local len1:dword
	local len2:dword
	local maxLen:dword
	local maxLenToAdd:dword
	local ln1:number
	local ln2:number
	local ov:byte
	local overflowCntrOffset:dword

	mov [overflowCntrOffset], 0
	mov [ov], 0

	;load signs
	mov eax, n1
	mov al, [eax].number.sign
	.if al == 1
		mov [n1isNeg], 1
	.else
		mov [n1isNeg], 0
	.endif

	mov eax, [n2]
	mov al, [eax].number.sign
	.if al == 1
		mov [n2isNeg], 1
	.else
		mov [n2isNeg], 0
	.endif
	;a - b
	.if [n1isNeg] == 0 && [n2isNeg] == 0
		invoke nCmp, [n1], [n2]
		.if eax == 1
			mov eax, [n1]
			mov cl, [eax].number.sign
			mov [ln1].number.sign, cl
			mov ecx, [eax].number.nptr
			mov [ln1].number.nptr, ecx
			mov ecx, [eax].number.nlen
			mov [ln1].number.nlen, ecx

			mov eax, [n2]
			mov cl, [eax].number.sign
			mov [ln2].number.sign, cl
			mov ecx, [eax].number.nptr
			mov [ln2].number.nptr, ecx
			mov ecx, [eax].number.nlen
			mov [ln2].number.nlen, ecx

			mov eax, [res]
			mov [eax].number.sign, 0
		.elseif eax == -1
			mov eax, [n1]
			mov cl, [eax].number.sign
			mov [ln2].number.sign, cl
			mov ecx, [eax].number.nptr
			mov [ln2].number.nptr, ecx
			mov ecx, [eax].number.nlen
			mov [ln2].number.nlen, ecx

			mov eax, [n2]
			mov cl, [eax].number.sign
			mov [ln1].number.sign, cl
			mov ecx, [eax].number.nptr
			mov [ln1].number.nptr, ecx
			mov ecx, [eax].number.nlen
			mov [ln1].number.nlen, ecx

			mov eax, [res]
			mov [eax].number.sign, 1
		.else 
			invoke calloc, 4, 1
			mov dword ptr [eax], 0
			mov ebx, [res]
			mov [ebx].number.nptr, eax
			mov [ebx].number.nlen, 1
			mov [ebx].number.sign, 0
			mov eax, ebx
			ret
		.endif
	; -a - (-b) = -a + b
	.elseif [n1isNeg] == 1 && [n2isNeg] == 1
		invoke nCmp, [n1], [n2]
		.if eax == 1
			mov eax, [n2]
			mov cl, [eax].number.sign
			mov [ln2].number.sign, cl
			mov ecx, [eax].number.nptr
			mov [ln2].number.nptr, ecx
			mov ecx, [eax].number.nlen
			mov [ln2].number.nlen, ecx

			mov eax, [n1]
			mov cl, [eax].number.sign
			mov [ln1].number.sign, cl
			mov ecx, [eax].number.nptr
			mov [ln1].number.nptr, ecx
			mov ecx, [eax].number.nlen
			mov [ln1].number.nlen, ecx

			mov eax, [res]
			mov [eax].number.sign, 1
		.elseif eax == -1
			mov eax, [n1]
			mov cl, [eax].number.sign
			mov [ln2].number.sign, cl
			mov ecx, [eax].number.nptr
			mov [ln2].number.nptr, ecx
			mov ecx, [eax].number.nlen
			mov [ln2].number.nlen, ecx

			mov eax, [n2]
			mov cl, [eax].number.sign
			mov [ln1].number.sign, cl
			mov ecx, [eax].number.nptr
			mov [ln1].number.nptr, ecx
			mov ecx, [eax].number.nlen
			mov [ln1].number.nlen, ecx

			mov eax, [res]
			mov [eax].number.sign, 0
		.else 
			invoke calloc, 4, 1
			mov dword ptr [eax], 0
			mov ebx, [res]
			mov [ebx].number.nptr, eax
			mov [ebx].number.nlen, 1
			mov [ebx].number.sign, 0
			mov eax, ebx
			ret
		.endif
	.else
		; - a - b = -(a + b)
		.if [n1isNeg] == 1 && [n2isNeg] == 0
			mov eax, [n1]
			mov [ln2].number.sign, 0
			mov ecx, [eax].number.nptr
			mov [ln2].number.nptr, ecx
			mov ecx, [eax].number.nlen
			mov [ln2].number.nlen, ecx

			mov eax, [n2]
			mov [ln1].number.sign, 0
			mov ecx, [eax].number.nptr
			mov [ln1].number.nptr, ecx
			mov ecx, [eax].number.nlen
			mov [ln1].number.nlen, ecx

			invoke nAdd, addr [ln1], addr [ln2], [res]
			mov ecx, [res]
			mov [ecx].number.sign, 1
			mov eax, [res]
			ret
		; b - (-a) =  b + a
		.elseif n1isNeg == 0 && n2isNeg == 1
			mov eax, [n1]
			mov [ln2].number.sign, 0
			mov ecx, [eax].number.nptr
			mov [ln2].number.nptr, ecx
			mov ecx, [eax].number.nlen
			mov [ln2].number.nlen, ecx

			mov eax, [n2]
			mov [ln1].number.sign, 0
			mov ecx, [eax].number.nptr
			mov [ln1].number.nptr, ecx
			mov ecx, [eax].number.nlen
			mov [ln1].number.nlen, ecx

			invoke nAdd, addr [ln1], addr [ln2], [res]
			mov ecx, [res]
			mov [ecx].number.sign, 0
			mov eax, [res]
			ret
		.endif
	.endif

	mov eax, [ln1].number.nlen
	mov [len1], eax
	mov eax, [ln2].number.nlen
	mov [len2], eax

	.if [len1] > eax
		mov eax, [len1]
		mov [maxLen], eax
	.else 
		mov [maxLen], eax
	.endif

	mov eax, [maxLen]
	mov [maxLenToAdd], eax

	invoke calloc, [maxLen], 4
	mov ebx, [res]
	mov [ebx].number.nptr, eax 
	mov ecx, [maxLen]
	mov [ebx].number.nlen, ecx 	

	mov edx, [res]
	mov edx, [edx].number.nptr
	mov esi, [ln1].number.nptr
	mov edi, [ln2].number.nptr
		
	.while [maxLen] != 0
		.if [len1] != 0
			mov eax, [esi]
		.else
			mov eax, 0
		.endif
		.if [len2] != 0
			mov ebx, [edi]	
		.else 
			mov ebx, 0
		.endif
		sub eax, ebx
		.if CARRY?
			mov [ov], 1
		.endif
		add [edx], eax

		.while [ov] == 1
			add edx, 4
			dec dword ptr [edx]
			.if ZERO?
				mov [ov], 1
			.else
				mov [ov], 0
			.endif
			inc [overflowCntrOffset]
			mov eax, [maxLen]
			dec eax
			.if [overflowCntrOffset] >= eax
				mov [ov], 0
				.break
			.endif
		.endw
		mov eax, [overflowCntrOffset]
		mov ebx, 4
		push edx
		mul ebx
		pop edx
		sub edx, eax
		mov [overflowCntrOffset], 0


		add edx, 4
		add esi, 4	
		add edi, 4
		.if [len1] != 0
			dec [len1]
		.endif
		.if [len2] != 0
			dec [len2]
		.endif
		dec [maxLen]
	.endw
	
	mov ecx, [res]
	mov ecx, [ecx].number.nptr
	mov eax, [maxLenToAdd]
	mov ebx, 4
	mul ebx
	add ecx, eax
	
	mov eax, [res]
	mov eax, [eax].number.nptr
	ret
nSub endp

nAdd proc uses eax ebx ecx edx edi esi n1:ptr number, n2:ptr number, res:ptr number
	local n1isNeg:byte
	local n2isNeg:byte
	local len1:dword
	local len2:dword
	local maxLen:dword
	local maxLenToAdd:dword
	local overflowCntrOffset:dword
	local ov:byte
	local buffToRealloc:dword
	local ediLen:dword
	local esiLen:dword
	local n1p:dword
	local n2p:dword
	local resp:dword
	local ln1:number
	local ln2:number

	mov [overflowCntrOffset], 0
	mov [ov], 0

	;load signs
	mov eax, [n1]
	mov al, [eax].number.sign
	.if al == 1
		mov [n1isNeg], 1
	.else
		mov [n1isNeg], 0
	.endif

	mov eax, [n2]
	mov al, [eax].number.sign
	.if al == 1
		mov [n2isNeg], 1
	.else
		mov [n2isNeg], 0
	.endif
	
	;determine what do you actually need
	.if [n1isNeg] == 1 && [n2isNeg] == 1
		mov eax, [res]
		mov [eax].number.sign, 1
	.elseif [n1isNeg] == 0 && [n2isNeg] == 0
		mov eax, [res]
		mov [eax].number.sign, 0
		; -a + b -> b - a -> b + a and sub is going to do b - a
	.elseif [n1isNeg] == 1 && [n2isNeg] == 0
		mov eax, [n1]
		mov [ln2].number.sign, 0
		mov ecx, [eax].number.nptr
		mov [ln2].number.nptr, ecx
		mov ecx, [eax].number.nlen
		mov [ln2].number.nlen, ecx

		mov eax, [n2]
		mov cl, [eax].number.sign
		mov [ln1].number.sign, cl
		mov ecx, [eax].number.nptr
		mov [ln1].number.nptr, ecx
		mov ecx, [eax].number.nlen
		mov [ln1].number.nlen, ecx
		invoke nSub, addr [ln1], addr [ln2], [res]
		ret
		; b - a -> b + a -> sub
	.elseif [n1isNeg] == 0 && [n2isNeg] == 1
		mov eax, [n2]
		mov [ln2].number.sign, 0
		mov ecx, [eax].number.nptr
		mov [ln2].number.nptr, ecx
		mov ecx, [eax].number.nlen
		mov [ln2].number.nlen, ecx

		mov eax, [n1]
		mov [ln1].number.sign, 0
		mov ecx, [eax].number.nptr
		mov [ln1].number.nptr, ecx
		mov ecx, [eax].number.nlen
		mov [ln1].number.nlen, ecx
		invoke nSub, addr [ln1], addr [ln2], [res]
		ret
	.endif
	
	;load numbers
	mov eax, [n1]
	mov eax, [eax].number.nlen
	mov [len1], eax
	mov ebx, [n2]
	mov ebx, [ebx].number.nlen
	mov [len2], ebx
	.if eax > ebx
		mov [maxLen], eax
	.else 
		mov [maxLen], ebx
	.endif

	mov esi, [n1]
	mov eax, [esi].number.nlen
	mov [esiLen], eax
	mov esi, [esi].number.nptr
	mov [n1p], esi

	mov edi, [n2]
	mov eax, [edi].number.nlen
	mov [ediLen], eax
	mov edi, [edi].number.nptr
	mov [n2p], edi

	;allocating (maxLen + 4) bytes for res, also calloc will fill it with zeros
	mov eax, [maxLen]
	mov ebx, [res]
	mov [ebx].number.nlen, eax
	mov [maxLenToAdd], eax
	pushad
	inc [maxLen]
	invoke calloc, [maxLen], 4
	dec [maxLen]
	mov [buffToRealloc], eax
	mov [resp], eax
	mov edx, [res]
	mov [edx].number.nptr, eax
	popad

	;	íà÷èíàåì ñ ñàìûõ ìëàäøèõ ðàçÿðäîâ, ïîêà ÷èñëà íå êîí÷àþòñÿ (ýòî îïðåäåëÿåòñÿ ïî äëèíå) 
	;	ìû êëàäåì èõ â íóæíûå ðåãèñòðû, èíà÷å ìû êëàäåì òóäà íóëè ÷òîáû ñêëàäûâàòü îñòàâøèåñÿ ÷àñòè áîëüøåãî ÷èñëà
	;	åñëè ìû âñòðå÷àåì ïåðåïîëíåíèå, òî óâåëè÷èâàåì ñëåäóþùèé ðàçðÿä äî òåõ ïîêà, ïîêà íå âñòðåòèì ïîñëåäíèé ðàçðÿä
	;	(îí íèêîãäà íå áûâàåò ïåðåïîëíåííûé), ëèáî ïîêà íå áóäåò inc áåç ïåðåïîëíåíèÿ
	.while [maxLen] != 0
		.if [ediLen] != 0
			mov eax, dword ptr [n2p]
			mov eax, [eax]
		.else
			mov eax, 0
		.endif
		.if [esiLen] != 0
			mov ebx, dword ptr [n1p]
			mov ebx, [ebx]
		.else
			mov ebx, 0
		.endif
		add ebx, eax
		.if CARRY?
			mov [ov], 1
		.endif
		mov eax, [resp]
		add [eax], ebx
		.if ZERO? && ebx != 0
			mov ov, 1
		.endif

		.while [ov] == 1 
			add [resp], 4
			mov eax, [resp]
			inc dword ptr [eax]
			.if CARRY?
				mov [ov], 1
			.else
				mov [ov], 0
			.endif
			inc [overflowCntrOffset]
		.endw
		mov eax, [overflowCntrOffset]
		mov ebx, 4
		mul ebx
		sub [resp], eax
		mov [overflowCntrOffset], 0

		mov ecx, 4
		add [resp], 4
		add [n1p], ecx
		add [n2p], ecx
		.if [ediLen] != 0
			dec [ediLen]
		.endif
		.if [esiLen] != 0
			dec [esiLen]
		.endif
		dec [maxLen]
	.endw

	mov ecx, [res]
	mov ecx, [ecx].number.nptr
	mov ebx, 4
	mov eax, [maxLenToAdd]
	mul ebx
	add ecx, eax

	;delete unneeded 4 bytes if so
	.if dword ptr [ecx] == 0
		invoke realloc, [buffToRealloc], eax
		mov ecx, [res]
		mov [ecx].number.nptr, eax 
	.else
		mov eax, [res]
		add [eax].number.nlen, 1
	.endif

	ret
nAdd endp

nAnd proc uses eax ebx ecx edx edi esi n1:ptr number, n2:ptr number, res:ptr number
	local len1:dword
	local len2:dword
	local minLen:dword

	;load sizes
	mov eax, [n1]
	mov ecx, [eax].number.nlen
	mov [len1], ecx
	mov eax, [n2]
	mov ebx, [eax].number.nlen
	mov [len2], ebx

	;find min size
	.if ecx > ebx
		mov [minLen], ebx
	.else
		mov [minLen], ecx
	.endif

	;load sign, minSize and allocate mem
	mov ecx, [res]
	mov eax, [minLen]
	mov [ecx].number.nlen, eax
	mov [ecx].number.sign, 0
	invoke calloc, eax, 4
	mov ecx, [res]
	mov [ecx].number.nptr, eax


	mov edi, [n1]
	mov edi, [edi].number.nptr
	mov esi, [n2]
	mov esi, [esi].number.nptr
	mov edx, [res]
	mov edx, [edx].number.nptr
	.while [len1] > 0 && [len2] > 0
		mov ebx, [edi]
		mov ecx, [esi]
		and ebx, ecx
		mov [edx], ebx
		add edx, 4
		add edi, 4
		add esi, 4
		dec [len1]
		dec [len2]
	.endw


	ret
nAnd endp

nXor proc uses eax ebx ecx edx edi esi n1:ptr number, n2:ptr number, res:ptr number
	local len1:dword
	local len2:dword
	local maxLen:dword

	;load sizes
	mov eax, [n1]
	mov ecx, [eax].number.nlen
	mov [len1], ecx
	mov eax, [n2]
	mov ebx, [eax].number.nlen
	mov [len2], ebx

	;find max size
	.if ecx > ebx
		mov [maxLen], ecx
	.else
		mov [maxLen], ebx
	.endif

	;load sign, maxLen and allocate mem
	mov ecx, [res]
	mov eax, [maxLen]
	mov [ecx].number.nlen, eax
	mov [ecx].number.sign, 0
	invoke calloc, eax, 4
	mov ecx, [res]
	mov [ecx].number.nptr, eax


	mov edi, [n1]
	mov edi, [edi].number.nptr
	mov esi, [n2]
	mov esi, [esi].number.nptr
	mov edx, [res]
	mov edx, [edx].number.nptr
	.while [len1] > 0 && [len2] > 0
		mov ebx, [edi]
		mov ecx, [esi]
		xor ebx, ecx
		mov [edx], ebx
		add edx, 4
		add edi, 4
		add esi, 4
		dec [len1]
		dec [len2]
	.endw

	;find which num is still not null
	.if [len1] > 0
		mov eax, [len1]
		mov esi, edi
	.else
		mov eax, [len2]
	.endif

	.while eax != 0
		mov ebx, [esi]
		mov [edx], ebx
		add esi, 4
		add edx, 4
		dec eax		
	.endw

	ret
nXor endp

nOr proc uses eax ebx ecx edx edi esi n1:ptr number, n2:ptr number, res:ptr number
	local len1:dword
	local len2:dword
	local maxLen:dword

	;load sizes
	mov eax, [n1]
	mov ecx, [eax].number.nlen
	mov [len1], ecx
	mov eax, [n2]
	mov ebx, [eax].number.nlen
	mov [len2], ebx

	;find max size
	.if ecx > ebx
		mov [maxLen], ecx
	.else
		mov [maxLen], ebx
	.endif

	;load sign, maxLen and allocate mem
	mov ecx, [res]
	mov eax, [maxLen]
	mov [ecx].number.nlen, eax
	mov [ecx].number.sign, 0
	invoke calloc, eax, 4
	mov ecx, [res]
	mov [ecx].number.nptr, eax

	mov edi, [n1]
	mov edi, [edi].number.nptr
	mov esi, [n2]
	mov esi, [esi].number.nptr
	mov edx, [res]
	mov edx, [edx].number.nptr
	.while [len1] > 0 && [len2] > 0
		mov ebx, [edi]
		mov ecx, [esi]
		or ebx, ecx
		mov [edx], ebx
		add edx, 4
		add edi, 4
		add esi, 4
		dec [len1]
		dec [len2]
	.endw

	;find which num is still not null
	.if [len1] > 0
		mov eax, [len1]
		mov esi, edi
	.else
		mov eax, [len2]
	.endif

	.while eax != 0
		mov ebx, [esi]
		mov [edx], ebx
		add esi, 4
		add edx, 4
		dec eax		
	.endw

	ret
nOr endp

nMulByInt proc uses eax ebx ecx edx esi n:ptr number, i:dword, res:ptr number
	local resp:dword
	local np:dword
	local len:dword
	local maxLen:dword
	local ov:byte
	local overflowCntrOffset:dword

	mov [overflowCntrOffset], 0
	mov [ov], 0

	mov eax, [res]
	mov ebx, [n]
	.if [ebx].number.sign == 1
		mov [eax].number.sign, 1
	.else
		mov [eax].number.sign, 0
	.endif
	
	mov eax, n
	mov eax, [eax].number.nlen
	mov [len], eax
	mov [maxLen], eax
	inc [maxLen]
	
	invoke calloc, [maxLen], 4
	mov [resp], eax
	mov ebx, [res]
	mov [ebx].number.nptr, eax
	mov eax, [maxLen]
	mov [ebx].number.nlen, eax

	mov esi, [n]
	mov esi, [esi].number.nptr
	mov [np], esi
	
	.while [maxLen] != 1
		mov eax, dword ptr [np]
		mov eax, [eax]
		mov ecx, i
		mul ecx
		mov ebx, dword ptr [resp]
		add [ebx], eax

		.while CARRY? || ov == 1
			add [resp], 4
			mov eax, [resp]
			inc dword ptr [eax]
			.if CARRY?
				mov [ov], 1
			.else
				mov [ov], 0
			.endif
			inc [overflowCntrOffset]
		.endw
		mov eax, [overflowCntrOffset]
		mov ebx, 4
		push edx
		mul ebx
		pop edx
		sub [resp], eax
		mov [overflowCntrOffset], 0

		.if edx != 0
			add [resp], 4
			mov eax, dword ptr [resp]
			add [eax], edx
			sub [resp], 4
		.endif

		add [resp], 4
		add [np], 4
		dec [maxLen]
	.endw

	mov esi, dword ptr [resp]
	mov esi, [esi]
	.if esi == 0
		mov esi, [res]
		dec [esi].number.nlen
		mov esi, [esi].number.nptr

		mov eax, [len]
		mov ebx, 4
		mul ebx
		invoke realloc, esi, eax
	.endif
	
	ret
nMulByInt endp

nPrint proc uses eax ebx ecx edx esi n:ptr number
	mov ebx, [n]
	mov eax, [ebx].number.nlen
	dec eax							;mov ptr to the end of num
	mov cl, [ebx].number.sign
	.if cl == 1
		pushad
		invoke printf, addr minus
		popad
	.endif
	mov esi, [ebx].number.nptr
	mov edi, 4
	mul edi
	add esi, eax
	mov eax, n
	mov eax, [eax].number.nlen

	;print
	.while eax != 0
		mov edx, [esi]
		.if edx == 0
			pushad
			invoke printf, addr zeros
			popad
		.else
			pushad
			invoke printf, addr fHex, edx 
			popad
		.endif
		sub esi, 4
		dec eax
	.endw
	invoke printf, addr newline

	mov eax, 0
	ret
nPrint endp

nDestroy proc uses eax ebx ecx edx n:ptr number
	mov ebx, [n]
	mov [ebx].number.nlen, 0
	mov [ebx].number.sign, 0
	invoke free, [ebx].number.nptr
	mov [ebx].number.nptr, 0
	
	ret
nDestroy endp

nMul proc n1:ptr number, n2:ptr number, res:ptr number
	local len1:dword
	local len2:dword
	local minLen:dword
	local maxLen:dword
	local n1Neg:byte
	local n2Neg:byte
	local shiftingCntr:dword
	local minPtr:dword
	local n1isMax:byte
	local mres:number
	local resCopy:number
	

	invoke nInitByInt, [res], 0

	mov eax, [n1]
	mov bl, [eax].number.sign
	mov [n1Neg], bl
	mov eax, [eax].number.nlen
	mov [len1], eax	

	mov eax, [n2]
	mov bl, [eax].number.sign
	mov [n2Neg], bl
	mov eax, [eax].number.nlen
	mov [len2], eax

	.if eax > [len1]
		mov [maxLen], eax
		mov eax, [len1]
		mov [minLen], eax
		mov eax, [n1]
		mov eax, [eax].number.nptr
		mov [minPtr], eax
		mov [n1isMax], 0
	.else
		mov [minLen], eax
		mov eax, [len1]
		mov [maxLen], eax
		mov eax, [n2]
		mov eax, [eax].number.nptr
		mov [minPtr], eax
		mov [n1isMax], 1
	.endif
	
	mov [shiftingCntr], 0
	mov ecx, [minLen]
	.while ecx != 0
		mov ebx, [minPtr]
		mov ebx, [ebx]
		.if [n1isMax] == 1
			invoke nMulByInt, [n1], ebx, addr [mres]
		.else
			invoke nMulByInt, [n2], ebx, addr [mres]
		.endif
		lea eax, [mres]
		mov [eax].number.sign, 0

		mov eax, [res]
		mov eax, [eax].number.nlen
		lea ebx, [resCopy]
		mov [ebx].number.nlen, eax
		
		mov eax, [res]
		mov eax, [eax].number.nptr
		lea ebx, [resCopy]
		mov [ebx].number.nptr, eax
		mov [ebx].number.sign, 0

		mov eax, [shiftingCntr]
		.while eax != 0
			push eax
			invoke nShl, addr [mres]
			pop eax
			dec eax
		.endw
		inc [shiftingCntr]
		add [minPtr], 4
		invoke nAdd, addr [mres], addr [resCopy], [res]
		invoke nDestroy, addr [resCopy]

		dec ecx
	.endw

	mov eax, [res]
	.if ([n1Neg] == 1 && [n2Neg] == 0) || ([n1Neg] == 0 && [n2Neg] == 1)
		mov [eax].number.sign, 1
	.else 
		mov [eax].number.sign, 0
	.endif
	
	ret
nMul endp

; ONLY lowercase letters: 1234567890abcdef
main proc c uses ebx argc:DWORD, argv:DWORD
	local n1:number
	local n2:number
	local res:number

	.if [argc] != 3 ; <prog name> <arg1> <arg2>
		invoke printf, addr er_wrong_argc
		mov eax, 1
		ret
	.endif

	mov eax, [argv]
	add eax, 4
	mov ebx, [eax]
	invoke isStringValid, ebx
	.if eax == 0
		invoke printf, addr er_wrong_arg
		mov eax, 1
		ret
	.endif

	mov eax, [argv]
	add eax, 4
	mov ebx, [eax]
	invoke nInitByStringHex, addr [n1], ebx
	invoke nPrint, eax
	
	mov eax, [argv]
	add eax, 8
	mov ebx, [eax]
	invoke isStringValid, ebx
	.if eax == 0
		invoke printf, addr er_wrong_arg
		mov eax, 1
		ret
	.endif
	
	mov eax, [argv]
	add eax, 8
	mov ebx, [eax]
	invoke nInitByStringHex, addr [n2], ebx
	invoke nPrint, eax

	invoke nAnd, addr [n1], addr [n2], addr [res]
	invoke printf, addr and_
	invoke nPrint, addr [res]
	invoke nDestroy, addr [res]

	invoke nXor, addr [n1], addr [n2], addr [res]
	invoke printf, addr xor_
	invoke nPrint, addr [res]
	invoke nDestroy, addr [res]

	invoke nOr, addr [n1], addr [n2], addr [res]
	invoke printf, addr or_
	invoke nPrint, addr [res]
	invoke nDestroy, addr [res]

	invoke nAdd, addr [n1], addr [n2], addr [res]
	invoke printf, addr add_
	invoke nPrint, addr [res]
	invoke nDestroy, addr [res]

	invoke nSub, addr [n1], addr [n2], addr [res]
	invoke printf, addr sub_	
	invoke nPrint, addr [res]
	invoke nDestroy, addr [res]

	invoke nMulByInt, addr [n1], 0ffffffffh, addr [res]
	invoke printf, addr mul_
	invoke nPrint, addr [res]
	invoke nDestroy, addr [res]

	invoke nMul, addr [n1], addr [n2], addr [res]
	invoke printf, addr mul__
	invoke nPrint, addr [res]
	invoke nDestroy, addr [res]

	mov eax, 0
	ret
main endp

end
