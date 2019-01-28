structure tigertips =
struct

type unique = unit ref

(* se agrega para manejar modos *)
datatype Mode = RO | RW  

datatype Tipo = TUnit
	| TNil
	| TInt of Mode
	| TString
	| TArray of Tipo  * unique
	| TRecord of (string * Tipo * int) list * unique
	| TTipo of string * Tipo option ref

end

