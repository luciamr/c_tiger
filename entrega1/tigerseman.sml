structure tigerseman :> tigerseman =
struct

open tigerabs
open tigersres
(* open tigertrans *)

type expty = {exp: exp, ty: Tipo}

type venv = (string, EnvEntry) tigertab.Tabla
type tenv = (string, Tipo) tigertab.Tabla

val tab_tipos : (string, Tipo) Tabla = tabInserList(
	tabNueva(),
	[("int", TInt RW), ("string", TString)])

val tab_vars : (string, EnvEntry) Tabla = tabInserList(
	tabNueva(),
	[("print", Func{level=mainLevel, label="print",
		formals=[TString], result=TUnit, extern=true}),
	("flush", Func{level=mainLevel, label="flush",
		formals=[], result=TUnit, extern=true}),
	("getchar", Func{level=mainLevel, label="getstr",
		formals=[], result=TString, extern=true}),
	("ord", Func{level=mainLevel, label="ord",
		formals=[TString], result=TInt RW, extern=true}),
	("chr", Func{level=mainLevel, label="chr",
		formals=[TInt RW], result=TString, extern=true}),
	("size", Func{level=mainLevel, label="size",
		formals=[TString], result=TInt RW, extern=true}),
	("substring", Func{level=mainLevel, label="substring",
		formals=[TString, TInt RW, TInt RW], result=TString, extern=true}),
	("concat", Func{level=mainLevel, label="concat",
		formals=[TString, TString], result=TString, extern=true}),
	("not", Func{level=mainLevel, label="not",
		formals=[TInt RW], result=TInt RW, extern=true}),
	("exit", Func{level=mainLevel, label="exit",
		formals=[TInt RW], result=TUnit, extern=true})
	])

fun tipoReal (TTipo (s, ref (SOME (t)))) = tipoReal t
  | tipoReal t = t

fun tiposIguales (TRecord _) TNil = true
  | tiposIguales TNil (TRecord _) = true 
  | tiposIguales (TRecord (_, u1)) (TRecord (_, u2 )) = (u1=u2)
  | tiposIguales (TArray (_, u1)) (TArray (_, u2)) = (u1=u2)
  | tiposIguales (TTipo (_, r)) b =
		let
			val a = case !r of
				SOME t => t
				| NONE => raise Fail "No debería pasar! (1)"
		in
			tiposIguales a b
		end
  | tiposIguales a (TTipo (_, r)) =
		let
			val b = case !r of
				SOME t => t
				| NONE => raise Fail "No debería pasar! (2)"
		in
			tiposIguales a b
		end
  (* para mantener la igualdad a pedar de los distintos modos *)
  | tiposIguales (TInt _) (TInt _) = true
  | tiposIguales a b = (a=b)

fun transExp(venv, tenv) =
	let fun error(s, p) = raise Fail ("Error -- línea "^Int.toString(p)^": "^s^"\n")
        fun isTInt ty = let val tr = tipoReal ty in tr = TInt RO orelse tr = TInt RW end
		fun trexp(VarExp v) = trvar(v)
		| trexp(UnitExp _) = {exp=(), ty=TUnit}
		| trexp(NilExp _)= {exp=(), ty=TNil}
		| trexp(IntExp(i, _)) = {exp=(), ty=TInt RO}
		| trexp(StringExp(s, _)) = {exp=(), ty=TString}
		| trexp(CallExp({func, args}, nl)) =
            let
                (* busca en venv el tipo que retorna la función *)  
                val (lev, lab, formals, res, ext) = case tabBusca(func, venv) of
                    SOME (Func {level, label, formals, result, extern}) => (level, label, formals, result, extern)
                    | SOME _ => error(func^" no es una funcion", nl)
                    | NONE => error(func^" no esta", nl)
                (* calcula expty para todos los argumentos *)
                val etargs' = List.map trexp args
                (* se queda solo con el tipo de los argumentos *)
                val targs' = List.map (fn {exp, ty} => ty) etargs'
	        in 
                (* checkea el tipo de los argumentos recibidos -targs- contra los declarados -formals- *)
                if List.all (fn (i, j) => tiposIguales i j) (ListPair.zip (formals, targs')) then {exp=(), ty=res}
                    else error(func^": mal invocada, error de tipo en argumentos", nl)
            end
		| trexp(OpExp({left, oper=EqOp, right}, nl)) =
			let
				val {exp=_, ty=tyl} = trexp left
				val {exp=_, ty=tyr} = trexp right
			in
				if tiposIguales tyl tyr andalso not (tyl=TNil andalso tyr=TNil) andalso tyl<>TUnit then {exp=(), ty=TInt RW}
					else error("Tipos no comparables", nl)
			end
		| trexp(OpExp({left, oper=NeqOp, right}, nl)) = 
			let
				val {exp=_, ty=tyl} = trexp left
				val {exp=_, ty=tyr} = trexp right
			in
				if tiposIguales tyl tyr andalso not (tyl=TNil andalso tyr=TNil) andalso tyl<>TUnit then {exp=(), ty=TInt RW}
					else error("Tipos no comparables", nl)
			end
		| trexp(OpExp({left, oper, right}, nl)) = 
			let
				val {exp=_, ty=tyl} = trexp left
				val {exp=_, ty=tyr} = trexp right
			in
				if tiposIguales tyl tyr then
					case oper of
						PlusOp => if isTInt tyl then {exp=(),ty=TInt RO} else error("Error de tipos", nl)
						| MinusOp => if isTInt tyl then {exp=(),ty=TInt RO} else error("Error de tipos", nl)
						| TimesOp => if isTInt tyl then {exp=(),ty=TInt RO} else error("Error de tipos", nl)
						| DivideOp => if isTInt tyl then {exp=(),ty=TInt RO} else error("Error de tipos", nl)
						| LtOp => if isTInt tyl orelse tipoReal tyl=TString then {exp=(),ty=TInt RW} else error("Error de tipos", nl)
						| LeOp => if isTInt tyl orelse tipoReal tyl=TString then {exp=(),ty=TInt RW} else error("Error de tipos", nl)
						| GtOp => if isTInt tyl orelse tipoReal tyl=TString then {exp=(),ty=TInt RW} else error("Error de tipos", nl)
						| GeOp => if isTInt tyl orelse tipoReal tyl=TString then {exp=(),ty=TInt RW} else error("Error de tipos", nl)
						| _ => raise Fail "No debería pasar! (3)"
				else error("Error de tipos", nl)
			end
		| trexp(RecordExp({fields, typ}, nl)) =
			let
				(* traduce cada expresión de fields *)
				val tfields = map (fn (sy,ex) => (sy, trexp ex)) fields

				(* busca el tipo *)
				val (tyr, cs) = case tabBusca(typ, tenv) of
					SOME t => (case tipoReal t of
						TRecord (cs, u) => (TRecord (cs, u), cs)
						| _ => error(typ^" no es de tipo record", nl))
					| NONE => error("Tipo inexistente ("^typ^")", nl)
				
				(* verificar que cada campo esté en orden y tenga una expresión del tipo que corresponde *)
				fun verificar [] [] = ()
				  | verificar (c::cs) [] = error("Faltan campos", nl)
				  | verificar [] (c::cs) = error("Sobran campos", nl)
				  | verificar ((s,t,_)::cs) ((sy,{exp,ty})::ds) =
						if s<>sy then error("Error de campo", nl)
						else if tiposIguales ty t then verificar cs ds
							 else error("Error de tipo del campo "^s, nl)
				val _ = verificar cs tfields
			in
				{exp=(), ty=tyr}
			end
		| trexp(SeqExp(s, nl)) =
			let	val lexti = map trexp s
				val exprs = map (fn{exp, ty} => exp) lexti
				val {exp, ty=tipo} = hd(rev lexti)
			in	{ exp=(), ty=tipo } end
		| trexp(AssignExp({var=SimpleVar s, exp}, nl)) =
            let
                val {exp=_, ty=tyv} = trvar (SimpleVar s, nl)
                val {exp=_, ty=tye} = trexp exp
            in
                (* verifica que no sea read only *)
                if (tipoReal tyv) = TInt RO then error("Asignación incorrecta, la variable "^s^" es de sólo lectura", nl)
                (* verifica que coincidan los tipos *)
                else if tiposIguales tyv tye then {exp=(), ty=TUnit}
                else error("Asignación incorrecta, no coinciden los tipos", nl)
            end
		| trexp(AssignExp({var, exp}, nl)) =
            let
                val {exp=_, ty=tyv} = trvar (var, nl)
                val {exp=_, ty=tye} = trexp exp
            in
                (* verifica que coincidan los tipos *)
                if tiposIguales tyv tye then {exp=(), ty=TUnit}
                else error("Asignación incorrecta, no coinciden los tipos", nl)
            end
		| trexp(IfExp({test, then', else'=SOME else'}, nl)) =
			let val {exp=testexp, ty=tytest} = trexp test
			    val {exp=thenexp, ty=tythen} = trexp then'
			    val {exp=elseexp, ty=tyelse} = trexp else'
			in
				if isTInt tytest andalso tiposIguales tythen tyelse then {exp=(), ty=tythen}
				else error("Error de tipos en if" ,nl)
			end
		| trexp(IfExp({test, then', else'=NONE}, nl)) =
			let val {exp=exptest,ty=tytest} = trexp test
			    val {exp=expthen,ty=tythen} = trexp then'
			in
				if isTInt tytest andalso tythen=TUnit then {exp=(), ty=TUnit}
				else error("Error de tipos en if", nl)
			end
		| trexp(WhileExp({test, body}, nl)) =
			let
				val ttest = trexp test
				val tbody = trexp body
			in
				if isTInt (#ty ttest) andalso #ty tbody = TUnit then {exp=(), ty=TUnit}
				else if not (isTInt (#ty ttest)) then error("Error de tipo en la condición", nl)
				else error("El cuerpo de un while no puede devolver un valor", nl)
			end
		| trexp(ForExp({var, escape, lo, hi, body}, nl)) =
            let
                val {exp=_, ty=tylo} = trexp lo
                val {exp=_, ty=tyhi} = trexp hi
                val venv' = tabRInserta (var, Var {ty=TInt RO}, venv)
                val {exp=_, ty=tybody} = transExp (venv', tenv) body
            in
                 if (isTInt tylo) andalso (isTInt tyhi) andalso tipoReal tybody = TUnit then {exp=(), ty=TUnit}
                 else if not (isTInt tylo) then error("Error de tipo en la cota inferior", nl)
                 else if not (isTInt tyhi) then error("Error de tipo en la cota superior", nl)
                 else error("Error de tipo en el cuerpo del for", nl)
            end
		| trexp(LetExp({decs, body}, _)) =
			let
				val (venv', tenv', _) = List.foldl (fn (d, (v, t, _)) => trdec(v, t) d) (venv, tenv, []) decs
				val {exp=expbody,ty=tybody}=transExp (venv', tenv') body
			in 
				{exp=(), ty=tybody}
			end
		| trexp(BreakExp nl) =
			{exp=(), ty=TUnit} (*COMPLETAR*)
		| trexp(ArrayExp({typ, size, init}, nl)) =
            let
                (* verifica que exista el tipo *)
                val tr = case tabBusca(typ, tenv) of
                            SOME t => tipoReal t
                            | NONE => error("No existe el tipo "^typ, nl)
                (* obtiene el tipo del array *)
                val aty = case tr of
                            TArray (t, _) => t
                            | _ => error("Error de tipo, "^typ^" no es un array", nl)
                val {exp=_, ty=tys} = trexp size
                val {exp=_, ty=tyi} = trexp init
            in
                if (isTInt tys) andalso (tiposIguales aty tyi) then {exp=(), ty=tr}
                (* TODO chequear que sea positivo *)
                else if not (isTInt tys) then error("El tamaño del arreglo debe ser entero", nl)
                else error("No coinciden los tipos", nl)
            end
		and trvar(SimpleVar s, nl) =
            let
                val tyv = case tabBusca(s, venv) of
                    SOME(Var {ty}) => ty
                    | SOME _ => error(s^" no es una variable", nl)
                    | NONE => error("La variable "^s^" no existe", nl)
            in
                {exp=(), ty=tyv}
            end
		| trvar(FieldVar(v, s), nl) =
            let
                (* verifica que sea un record y obtiene el listado de fields*)
                val {exp=_, ty=tyv} = trvar (v, nl)
                val listf = case (tipoReal tyv) of
                            TRecord (f, _) => f
                            | _ => error("No es de tipo record", nl)
                (* verifica que el field buscado exista y recupera su tipo *)
                fun getFieldType s [] = error("No existe el field "^s, nl)
                    | getFieldType s ((s', t', i')::f') = if (s = s') then t' else getFieldType s f'
                val tyf = getFieldType s listf
            in
                {exp=(), ty=tyf}
            end
		| trvar(SubscriptVar(v, e), nl) =
            let
                (* obtiene el tipo del arreglo *)
                val {exp=_, ty=tyv} = trvar (v, nl)
                val tr = case (tipoReal tyv) of
                            TArray (t, _) => t
                            | _ => error("No es de tipo array", nl)
                (* obtiene el tipo de la expresión *)
                val {exp=_, ty=tye} = trexp e
            in
                if isTInt tye then {exp=(), ty=tr}
                (* TODO chequear que sea positivo *)
                else error("El índice tiene que ser entero", nl)
            end
		and trdec (venv, tenv) (VarDec ({name,escape,typ=NONE,init},pos)) =
                let
                    val {exp=expe, ty=tye} = transExp (venv, tenv) init
                    val venv' = tabRInserta (name, Var {ty=tye}, venv)
                in
                    if tye <> TNil then (venv', tenv, [])
                    else error("Sólo los records pueden inicializarse en null, no indicó el tipo de la variable", pos)
                end        
		| trdec (venv,tenv) (VarDec ({name,escape,typ=SOME s,init},pos)) =
                let
                    val {exp=expe, ty=tye} = transExp (venv, tenv) init
                    (* chequea que el tipo exista *)
                    val s' = case tabBusca(s, tenv) of
                                SOME t => t
                                | NONE => error("El tipo "^s^" no existe", pos)
                    val venv' = tabRInserta (name, Var {ty=tye}, venv)
                in
                    if tye <> TNil andalso tiposIguales s' tye then (venv', tenv, [])
                    (* permite que los records se inicializen en null *)
                    else if tye = TNil then case s' of
                                                (TRecord _) => (venv', tenv, [])
                                                | _ => error("Sólo los records pueden inicializarse en null, debe inicializar la variable", pos)
                    else error("No coinciden los tipos", pos)
                end        
		| trdec (venv,tenv) (FunctionDec fs) =
			(venv, tenv, []) (*COMPLETAR*)
		| trdec (venv,tenv) (TypeDec ts) =
			(venv, tenv, []) (*COMPLETAR*)
	in trexp end
fun transProg ex =
	 let	val main =
				LetExp({decs=[FunctionDec[({name="_tigermain", params=[],
								result=NONE, body=ex}, 0)]],
						body=UnitExp 0}, 0)
		val _ = transExp(tab_vars, tab_tipos) main
	in	print "bien!\n" end
end
