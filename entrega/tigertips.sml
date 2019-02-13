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

fun printTipo TUnit = "TUnit"
	| printTipo TNil = "TNil"	
	| printTipo (TInt RO) = "TInt RO"
	| printTipo (TInt RW) = "TInt RW"
	| printTipo TString = "TString"
	| printTipo (TArray (t, _)) = "TArray of ("^printTipo t^")"
	| printTipo (TRecord (fs, _)) = "TRecord "^List.foldl (fn ((n, t, p),res) => "("^n^"::"^printTipo t^"); "^res) "" fs
	| printTipo (TTipo (s, r)) = (case !r of
				                    NONE => "ttipo "^s^" none"
				                    | SOME t => "ttipo "^s^" ("^printTipo t^")")       

end
