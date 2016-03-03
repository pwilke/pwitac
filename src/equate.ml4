open Term
      
(* Pretty print a term *)
let string_of_constr x = Pp.string_of_ppcmds (Termops.print_constr x)

type ('a,'b) either =
  Left of 'a
  | Right of 'b
       
(* for debugging purposes *)
let string_of_kind =
  function
    Rel i -> "rel"
    | Var n -> "var"
    | Meta mv -> "meta"
    | Evar e -> "evar"
    | Sort s -> "sort"
    | Cast (c,k,t) -> "cast"
    | Prod (n,t,t') -> "prod"
    | Lambda (n,t,c) -> "lambda"
    | LetIn (n,c,t,c') -> "letin"
    | App (c,c') -> "app"
    | Const c -> "constant"
    | Ind ind -> "ind"
    | Construct c -> "construct"
    | Case (ci,c,c',ca) -> "case"
    | Fix f -> "fix"
    | CoFix cf -> "cofix"


let string_of_constr_list (l: Term.constr list) =
  String.concat "," (List.map string_of_constr l)

type sgn = Pos | Neg

let inv_sgn = function
    Pos -> Neg
  | Neg -> Pos

let isgn (a,b) = (a,inv_sgn b)
             
let list_of_zadd zadd_term zsub_term c :  (Term.constr * sgn) list =
  let rec aux c = 
    match Term.kind_of_term c with
      Term.Var x -> [c,Pos]
    | Term.App (f, args) ->
       if Term.eq_constr f zadd_term
       then
         let (lhs,rhs) = (args.(0), args.(1)) in
         aux lhs @ aux rhs
       else if Term.eq_constr f zsub_term
       then
         let (lhs,rhs) = (args.(0), args.(1)) in
         aux lhs @ (List.map isgn (aux rhs))
       else [c,Pos]
    | k ->  [c,Pos]
  in aux c

let norm lhs rhs =
  let (lhsp,lhsn) = lhs |> List.partition (fun (_,s) -> s = Pos) in
  let (rhsp,rhsn) = rhs |> List.partition (fun (_,s) -> s = Pos) in
  (List.map fst (lhsp @ rhsn)),
  (List.map fst (rhsp @ lhsn))
         
(* partitions lists of constr between those that are (Var x) and the others*)
let part x l =
  l |> List.partition (fun c ->
           if isVar c then
             let i = destVar c in
             Names.id_ord i x = 0
           else false)

let mkadd zadd zero l =
  let rec aux l =
  match l with
    [] -> zero
  | [a] -> a
  | a::r -> Term.mkApp (zadd,[|a;aux r|])
  in aux l
                      
let mkEquation zadd zsub zero lhs rhs x =
  let mksub a b = Term.mkApp (zsub,[|a;b|]) in
  let mkadd = mkadd zadd zero in
  let lhs, rhs = norm lhs rhs in
  let (lhsx, lhsnox) = part x lhs in
  let (rhsx, rhsnox) = part x rhs in
  match lhsx, rhsx with
    [], [] -> failwith "at least one side must contain the variable"
  | a::r, b::s  -> failwith "only one side must contain the variable"
  | [a], [] -> mksub (mkadd rhsnox) (mkadd lhsnox)
  | [], [a] -> mksub (mkadd lhsnox) (mkadd rhsnox)
  | a::r, _ | _, a::r -> failwith "only one occurence of the variable is permitted"
                                  

(* equate x H : assert (x = bla) from hypothesis H which is of the form (... + x + ... = A)  *)
let equate x h (gl: Proof_type.goal Tacmach.sigma) : Proof_type.goal list Evd.sigma =
  let hyp : Term.constr = Tacmach.pf_get_hyp_typ gl h in
  let open Term in
  match Term.kind_of_term hyp with
  | App(f,args) ->
     begin
       match kind_of_term f with
         Ind ind when (Libnames.eq_gr (Libnames.IndRef ind) Coqlib.glob_eq)
         ->
         let (lhs,rhs) = (args.(1), args.(2)) in
         (* copied from plugins/romega/const_omega.ml *)
         let z_module = [["Coq";"ZArith";"BinInt"]] in
         let bin_module = [["Coq";"Numbers";"BinNums"]] in
         let z_constant = Coqlib.gen_constant_in_modules "Omega" z_module in
         let bin_constant = Coqlib.gen_constant_in_modules "Omega" bin_module in
         let plus = z_constant "Z.add" in
         let minus = z_constant "Z.sub" in
         let zzero = bin_constant "Z0" in
         let ztyp = bin_constant "Z" in
         let t = mkEquation plus minus zzero (list_of_zadd plus minus lhs)
                            (list_of_zadd plus minus rhs) x in
         (* let s = string_of_constr t in *)
         (* failwith s *)
         (* (\* let s = string_of_ident_list (list_of_zadd plus lhs) ^ " = " ^ *\) *)
         (* (\*           string_of_ident_list (list_of_zadd plus rhs) in *\) *)
         (* (\* failwith s; *\) *)
         Tactics.assert_tac
           Names.Anonymous (Term.mkApp(Term.mkInd ind, [|ztyp;Term.mkVar x; t|]))
           gl
        
       | _ -> failwith "Expected hypothesis to be of type (_ = _)."
     end
  | _ -> failwith "BLAAAAA"

TACTIC EXTEND equate_x
| ["equate" ident(x) ident(h)] -> [equate x h]
END;;


