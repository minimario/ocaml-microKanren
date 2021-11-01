open Core;;

type variable = int
type term = 
    | Variable of variable
    | Value of int
    | TermList of term list

type substitution = (variable * term) list;;
type state = substitution * int
type 
    immature_stream = unit -> stream and 
    stream = 
    | Empty_stream
    | Mature_stream of state * stream 
    | Immature_stream of immature_stream

type goal = state -> stream
(* type stream =  *)

(* walk :: term -> substitution -> term *)
let walk (var : term) (substitution : substitution) =
    match var with 
    | Variable v -> 
        (match List.Assoc.find substitution v ~equal:Int.equal with
        | Some term -> term
        | _ -> Variable v)
    | nonvariable -> nonvariable

let ext_s (var : variable) (term : term) (subst : substitution) = (var, term) :: subst 

let rec term_equal term1 term2 = 
    match term1, term2 with 
    | Variable v1, Variable v2 -> v1 = v2
    | Value v1, Value v2 -> v1 = v2
    | TermList v1, TermList v2 -> List.equal term_equal v1 v2
    | _ -> false

let rec unify u v subst = 
    let u_term = walk u subst in 
    let v_term = walk v subst in 
    match u_term, v_term with 
    | Variable u_var, Variable v_var when u_var = v_var -> subst
    | Variable u_var, v_term -> ext_s u_var v_term subst
    | u_term, Variable v_var -> ext_s v_var u_term subst
    | TermList u_list, TermList v_list ->
        let subst' = unify (List.hd_exn u_list) (List.hd_exn v_list) subst in
        let subst'' = unify (TermList (List.tl_exn u_list)) (TermList (List.tl_exn v_list)) subst' in
        subst''
    | u_term, v_term when term_equal u_term v_term -> subst
    | _ -> []

let mzero = Empty_stream
let unit s_c : stream = Mature_stream (s_c, mzero)
let equals u v : goal = 
    fun (substitution, counter) ->
        let s = unify u v substitution in
        if List.length s > 0 then unit (s, counter)
        else Empty_stream

let call_fresh (f : int -> state -> stream) : goal = 
    fun (substitution, counter) -> 
        f counter (substitution, counter + 1)
let rec mplus (s1 : stream) (s2 : stream) =
    match s1 with 
    | Empty_stream -> s2
    | Immature_stream _ -> (Immature_stream (fun () -> mplus s2 s1))
    | Mature_stream (state, stream) -> Mature_stream (state, mplus stream s2)        

let rec bind s (g : state -> stream) = match s with 
    | Empty_stream -> mzero
    | Immature_stream _ -> Immature_stream (fun () -> bind s g)
    | Mature_stream (state, stream) -> mplus (g state) (bind stream g)

let disj (g1 : state -> stream) (g2 : state -> stream) = 
    fun sc -> mplus (g1 sc) (g2 sc)
let conj (g1 : state -> stream) (g2 : state -> stream) = fun sc -> bind (g1 sc) g2 

let empty_state : state = ([], 0)

(* TESTING CODE STARTS HERE *)
let one_variable = 
    (call_fresh (fun q -> (equals (Variable q) (Value 5)))) empty_state

let a_and_b = 
    (conj 
        (call_fresh (fun a -> (equals (Variable a) (Value 7))))
        (call_fresh (
            (fun b -> disj (equals (Variable b) (Value 5)) (equals (Variable b) (Value 6)))
        ))
    )
    empty_state

let rec fives = 
    fun x ->
    (disj 
        (equals (Variable x) (Value 5))
        (fun sc ->
            Immature_stream (fun () -> ((fives x) sc))
        )
    )
let who_cares = call_fresh (fun q -> fives q) empty_state


let rec print_term term = match term with 
    | Variable v -> "Variable(" ^ string_of_int v ^ ")"
    | Value v -> "Value(" ^ string_of_int v ^ ")"
    | TermList tl -> 
        let terms = List.map ~f:print_term tl in
            "TermList " ^ (String.concat ~sep:", " terms)

let print_substitution subst = 
    let terms = List.map ~f:(fun (variable, term) ->
        "Variable(" ^ string_of_int variable ^ ") -> " ^ print_term term
    ) subst in 
    "[" ^ (String.concat ~sep:", " terms) ^ "]"
let main = 
    match who_cares with 
    | Mature_stream (state, _) ->
        let (substitution, next) = state in
        print_string ((print_substitution substitution) ^ ", " ^ string_of_int next ^ "\n")
    | _ -> print_string ":("