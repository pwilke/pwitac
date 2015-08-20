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

let is_applicable thm thm_ty gl c = 
  let try_apply thm_ty nprod =
    let n = Term.nb_prod thm_ty - nprod in
    if n<0 then
      Util.error "Applied theorem has not enough premisses.";
    let clause = Clenv.make_clenv_binding_apply gl (Some n) (thm,thm_ty) Glob_term.NoBindings in
    Clenvtac.res_pf clause ~with_evars:true ~flags:Unification.default_unify_flags gl
  in
  try ignore (try_apply thm_ty (Term.nb_prod c)); true
  with e -> false

(* is constructor i of inductive type ind applicable to goal gl? *)
let is_applicable_constr ind i gl c =
  let cd : Term.constr = Term.mkConstruct (ind, succ i) in
  let thm_ty = Reductionops.nf_betaiota (Tacmach.project gl) (Tacmach.pf_type_of gl cd) in
  is_applicable cd thm_ty gl c
		       
(* Get a list of constructors that are applicable to current goal. *)
let constructors env c gl =
  match safe_find_rectype env c with
    Right errmsg -> failwith ("constructors: "^errmsg)
  | Left (ind,args) ->
     let mindspec = Global.lookup_inductive ind in
     Util.array_fold_right_i
       (fun i v l ->
	if is_applicable_constr ind i gl c
	then ((Names.string_of_id ((snd mindspec).Declarations.mind_consnames.(i))),
	      string_of_constr v) :: l
	else l
       )
       (Inductive.type_of_constructors ind mindspec)
       []
	      
(* is hypothesis hyp applicable to goal gl? *)
let is_hyp_applicable hyp gl c =
  is_applicable (Term.mkVar (fst hyp)) (snd hyp) gl c
		       
(* Get a list of hypotheses that are applicable to current goal. *)
let hyps_applicable hyps c gl =
  List.fold_right
       (fun (name,typ) l ->
	if is_hyp_applicable (name,typ) gl c
	then (Names.string_of_id name , string_of_constr typ) :: l
	else l
       )
       hyps
       []

       
let applicable_constructors () =
  let p = Proof_global.give_me_the_proof () in
  let sgl = Proof.V82.subgoals p in
  let gl = {sgl with Evd.it=(List.hd sgl.Evd.it)} in
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
  let concl = Tacmach.pf_concl gl in
  let hyps : (Names.identifier * Term.types) list = Tacmach.pf_hyps_types gl in
  let l = hyps_applicable hyps concl gl in
  let applicable_hyps = String.concat "\n" (List.map (fun (a,b) -> a^": "^b) l) in
  Pp.message applicable_hyps

VERNAC COMMAND EXTEND PwilkeAppCons
["AppCons"] -> [applicable_constructors ()]
END
VERNAC COMMAND EXTEND PwilkeAppHyps
  | ["AppHyps"] -> [applicable_hypotheses ()]
END
