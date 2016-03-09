(* Pretty print a term *)
let string_of_constr x = Pp.string_of_ppcmds (Termops.print_constr x)

type ('a,'b) either =
  Left of 'a
  | Right of 'b
					     
(* Safe version of Inductive.find_rectype. The errors are caught. *)
let safe_find_rectype (env: Environ.env) (c: Term.constr) : ((Names.inductive * Term.constr list),string) either  =
  try Left (Inductive.find_rectype env c) with
    Not_found -> Right (Printf.sprintf "Couldn't find inductive type %s\n" (string_of_constr c))

		       
let current_subgoal () =
  let p = Proof_global.give_me_the_proof () in
  let sgl = Proof.V82.subgoals p in
  let gl = {sgl with Evd.it=(List.hd sgl.Evd.it)} in
  gl

let is_applicable thm gl =
  try ignore (Tactics.eapply thm gl); true
  with e -> false


(* is constructor i of inductive type ind applicable to goal gl? *)
let is_applicable_constr ind i gl =
  let cd : Term.constr = Term.mkConstruct (ind, succ i) in
  is_applicable cd gl
		       
(* Get a list of constructors that are applicable to current goal. *)
let constructors env c gl =
  match safe_find_rectype env c with
    Right errmsg -> failwith ("constructors: "^errmsg)
  | Left (ind,args) ->
     let mindspec = Global.lookup_inductive ind in
     Util.array_fold_right_i
       (fun i v l ->
	if is_applicable_constr ind i gl
	then ((Names.string_of_id ((snd mindspec).Declarations.mind_consnames.(i))),
	      string_of_constr v) :: l
	else l
       )
       (Inductive.type_of_constructors ind mindspec)
       []
	      
(* is hypothesis hyp applicable to goal gl? *)
let is_hyp_applicable hyp gl =
  is_applicable (Term.mkVar hyp) gl
		       
(* Get a list of hypotheses that are applicable to current goal. *)
let hyps_applicable hyps gl =
  List.fold_right
       (fun (name,typ) l ->
	if is_hyp_applicable name gl
	then (Names.string_of_id name , string_of_constr typ) :: l
	else l
       )
       hyps
       []

       
let applicable_constructors () =
  let gl = current_subgoal () in
  let concl = Tacmach.pf_concl gl in
  let l = constructors (Tacmach.pf_env gl) concl gl in
  let appcons = String.concat "\n" (List.map (fun (a,b) -> a^": "^b) l) in
  let n = List.length l in
  Pp.message (Printf.sprintf "%s\n%d constructor%s exist%s for that type (%s)"
			     appcons
			     n
			     (if n = 1 then "" else "s")
			     (if n = 1 then "s" else "")
			     (string_of_constr concl))

    
let applicable_hypotheses () =
  let gl = current_subgoal () in 
  let hyps : (Names.identifier * Term.types) list = Tacmach.pf_hyps_types gl in
  let l = hyps_applicable hyps gl in
  let applicable_hyps = String.concat "\n" (List.map (fun (a,b) -> a^": "^b) l) in
  Pp.message applicable_hyps

VERNAC COMMAND EXTEND PwilkeAppCons
["AppCons"] -> [applicable_constructors ()]
END
VERNAC COMMAND EXTEND PwilkeAppHyps
  | ["AppHyps"] -> [applicable_hypotheses ()]
END


