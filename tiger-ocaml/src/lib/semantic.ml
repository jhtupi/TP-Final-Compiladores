(* semantic.ml *)

module A = Absyn
module S = Symbol
module E = Env
module T = Types


let type_mismatch loc expected found =
	Error.error loc "type mismatch: expected %s, found %s" (T.string_of_ty expected) (T.string_of_ty found)

let undefined loc kind id =
	Error.error loc "undefined %s %s" kind (S.name id)

let misdefined loc kind id =
	Error.error loc "%s is not a %s" (S.name id) kind

let cannot_be_nil loc id =
	Error.error loc "cannot initialize untyped variable %s with nil" (S.name id)

let loc = Location.loc

let coerceable = T.coerceable

let look env kind id pos =
	match S.look id env with
	| Some x -> x
	| None -> undefined pos kind id

let tylook tenv id pos =
	look tenv "type" id pos

let funlook venv id pos =
	look venv "function" id pos

let varlook venv id pos =
	look venv "variable" id pos

let coerce ty1 ty2 pos =
	if not (coerceable ty1 ty2) then
		type_mismatch pos ty2 ty1

let check_int ty pos = coerce ty T.INT pos

let check_unit ty pos = coerce ty T.UNIT pos

let rec check_exp ((tenv,venv,in_loop) as env) (pos,exp) =
	match exp with
	| A.NilExp -> T.NIL

	| A.IntExp _ -> T.INT
	| A.StringExp -> T.STRING

	| A.ArrayExp (typeid, ((lsize,_) as size), elem) ->
		 let tsize = check_exp env size in
		 check_int tsize lsize;
		 let telem = check_exp env elem in
		 begin match T.actual_ty (tylook tenv typeid pos) with
		 | T.ARRAY (te,_) as t ->
				coerce telem te (loc elem);
				t
		 | _ -> misdefined pos "array type" typeid
		 end
	| A.RecordExp (typeid, ls) ->
			(* tipoRecord é o tipo do typeid *)
			let tipoRecord = actual_ty(tylook tenv typeid pos) in
			match tipoRecord with 
			| T.RECORD (lista_campos, _) ->
				let rec check_rec = function
					| [] -> tipoRecord
					(* Procura para cada elemento da lista, se o elemento é de acordo com o esperado *)
					| (name,exp)::rest -> 
						begin match (assoc_opt name lista_campos) with
						 | None -> Error.error "Field not defined"
						 | Some x -> coerce (check_exp env exp) x (loc exp);
						 check_rec rest
						end
				in
				check_rec ls
			(* Erro *)
			| _ -> type_mismatch (loc tipoRecord) T.RECORD tipoRecord

	| A.VarExp var -> check_var env var

	| A.AssignExp (var,exp) -> T.UNIT

	| A.CallExp (fun_name, parameters) -> T.UNIT (* ? *)

	| A.OpExp (op,l,r) ->
		let tl = check_exp env l in
		let tr = check_exp env r in
		begin match op with
		| A.PlusOp | A.MinusOp | A.TimesOp | A.DivideOp ->
			 check_int tl (loc l);
			 check_int tr (loc r);
			 T.INT
		| A.LtOp | A.GtOp | A.GeOp | LeOp ->
			if not (((coerceable tl T.INT) & (coerceable tr T.INT)) | ((coerceable tl T.STRING) & (coerceable tr T.STRING)))
					then (* tl não é tipo INT *)
					Error.error "Both sides are not the same type (INT or STRING)"
			else 
			T.INT
		| A.AndOp | OrOp -> 
			check_int tl (loc l);
			check_int tr (loc r);
			T.INT
		| A.EqOp | A.NeOp ->
		if not(coerceable tl tr) 
			then type_mismatch (loc tl) tl tr;
		else if not(coerceable tr tl)
			then type_mismatch (loc tr) tr tl;
			T.INT
		| _ ->
			 Error.fatal "unimplemented"
		end

	| A.IfExp (comparison, exp_then, exp_else) ->
		(* Verifica se a comparação é tipo inteiro *)
		check_int (check_exp env comparison) (loc comparison);

		let tipo_then = check_exp env exp_then in
		match exp_else with
		| Some exp ->
		  let tipo_else = check_exp env exp in
		  if coerceable tipo_then tipo_else then
		  	tipo_else
		  else if coerceable tipo_else tipo_then then
		  	tipo_then 
		  else Error.error "Types not compatibles"
		| None -> T.UNIT

	| A.While (comparison, exp) -> 
		(* Checa se a expressão de comparação é um inteiro *)
	  check_int (check_exp env comparison) (loc comparison);
	  check_unit (check_exp (tenv,venv,true) exp) (loc exp);
	  T.UNIT

	| A.ForExp (iterator, lower_bound, upper_bound, body) -> 
	(* checar se os bounds são do tipo int *)
	check_int (check_exp lower_bound) (loc lower_bound);
	check_int (check_exp upper_bound) (loc lower_bound);
	(* cria o iterador no ambiente *)
	let env' = S.enter venv iterator INT in
		check_exp (env',venv,true) body;
		T.UNIT

	| A.BreakExp -> 
		if(in_loop) then
			T.UNIT
		else 
			Error.error "Break outside of loop"

	| A.SeqExp exps ->
		 let rec check_seq = function
			 | []        -> T.UNIT
			 | [exp]     -> check_exp env exp
			 | exp::rest -> ignore (check_exp env exp); check_seq rest
		 in
		 check_seq exps

	| A.LetExp (decs,body) ->
		 let env' = List.fold_left check_dec env decs in
		 check_exp env' body

	| _ ->
		 Error.fatal "unimplemented"

and check_var ((tenv,venv,in_loop) as env) (pos,var) =
	match var with
	| A.SimpleVar id ->
		 begin match varlook venv id pos with
		 | T.FUNCTION _ -> misdefined pos "variable" id
		 | t -> t
		 end
	| A.FieldVar (var, symbol)-> T.UNIT (* ? *)

	| A.SubscriptVar (var, exp)-> 
		(* checa se a posição acessada é um inteiro *)
		check_int (check_exp env exp) (loc exp)
		(* ? *)


	| _ ->
		 Error.fatal "unimplemented"

and check_dec ((tenv,venv,in_loop) as env) (pos,dec) =
	match dec with
	| A.VarDec (name,type_opt,init) ->
		 let tinit = check_exp env init in
		 let tvar =
			 match type_opt with
			 | Some (pos,tname) -> let t = tylook tenv tname pos in
														 coerce tinit t (loc init);
														 t
			 | None -> if coerceable tinit T.NIL then
									 cannot_be_nil (loc init) name;
								 tinit
		 in
		 let venv' = S.enter name tvar venv in
		 (tenv,venv',in_loop)

	| A.MutualFunctionDecs -> T.UNIT (* ? *)

	| A.MutualTypeDecs tdecs ->
		 (* first pass: add new type names to environment *)
		 let new_tenv =
			 List.fold_left
				 (fun tenv (_pos, (tname, _tcons)) ->
					 S.enter tname (T.NAME (tname, ref None)) tenv)
				 tenv
				 tdecs
		 in
		 let new_env = (new_tenv, venv, in_loop) in
		 (* second pass: check type definition *)
		 List.iter
			 (fun (_pos, (tname, tcons)) ->
				 let ty = check_ty new_env tcons in
				 match S.look tname new_tenv with
				 | Some (T.NAME (_, cell)) -> cell := Some ty
				 | _ -> Error.fatal "bug!")
			 tdecs;
		 new_env

	| _ ->
		 Error.fatal "unimplemented"

and check_ty ((tenv,venv,in_loop) as env) (pos,ty) =
	match ty with
	| A.NameTy t -> tylook tenv t pos

	| A.RecordTy fields -> T.UNIT (* Não fala o que tem que fazer *)
	| A.ArrayTy ty -> T.UNIT (* Não fala o que tem que fazer *)
	| _ ->
		 Error.fatal "unimplemented"


let type_check program =
	check_exp (E.base_tenv, E.base_venv, false) program
