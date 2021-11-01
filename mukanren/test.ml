open OUnit2
open Mukanren
open Core

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

let rec appendo = fun l s out ->
    (disj
        (conj 
            (equals (TermList []) l)
            (equals s out)
        )
        (call_fresh (fun a -> (call_fresh (fun d ->
            (conj 
                (equals (TermList [Variable a; Variable d]) l))
                (call_fresh (fun res ->
                    (conj 
                        (equals (TermList [Variable a; Variable res]) out))
                        (fun sc -> Immature_stream (fun () -> (appendo (Variable d) s (Variable res) sc))
                    )
                ))
            )
        ))))
    

let call_appendo = (
    (call_fresh (fun q ->
        (call_fresh (fun l ->
            (call_fresh (fun s ->
                (call_fresh (fun out ->
                    (conj
                        (appendo (Variable l) (Variable s) (Variable out))
                        (equals (TermList [Variable l; Variable s; Variable out]) (Variable q))
                    )
                ))
            ))
        ))
    )) empty_state
)

let ground_appendo = (appendo (Value 3) (Value 6) (TermList [Value 3; Value 6])) empty_state

let rec print_term term = match term with 
    | Variable v -> "Variable(" ^ string_of_int v ^ ")"
    | Value v -> "Value(" ^ string_of_int v ^ ")"
    | TermList tl -> 
        let terms = List.map ~f:print_term tl in
            "TermList [" ^ (String.concat ~sep:", " terms) ^ "]"

let subst_to_string subst = 
    let terms = List.map ~f:(fun (variable, term) ->
        "Variable(" ^ string_of_int variable ^ ") -> " ^ print_term term
    ) subst in 
    "[" ^ (String.concat ~sep:", " terms) ^ "]"

let rec find_next_mature stream = match stream with 
    | Empty_stream -> Empty_stream
    | Mature_stream (state, stream) -> Mature_stream (state, stream)
    | Immature_stream is -> find_next_mature (is ())

let main = 
    match ground_appendo with 
    | Empty_stream -> print_string "empty"
    | Mature_stream (state, next_stream) ->
        let (substitution, next_counter) = state in
        print_string ((subst_to_string substitution) ^ ", " ^ string_of_int next_counter ^ "\n");
    | _ -> print_string ":("

(* let main = 
    match call_appendo with 
    | Mature_stream (state, next_stream) ->
        let (substitution, next_counter) = state in
        print_string ((subst_to_string substitution) ^ ", " ^ string_of_int next_counter ^ "\n");
        let next_mature = find_next_mature next_stream in
        (match next_mature with 
        | Mature_stream (state', next_stream') ->
            let (substitution', next_counter') = state' in
            print_string ((subst_to_string substitution') ^ ", " ^ string_of_int next_counter' ^ "\n");
        | _ -> print_string ":|")
    | _ -> print_string ":(" *)

(* let tests = "Test Suite for Microkanren" >::: [
    "one-variable" >::
    (fun _ ->
        match one_variable with 
        | Mature_stream (state, Empty_stream) ->
            let (substitution, next) = state in
            assert_equal (subst_to_string substitution) "[Variable(0) -> Value(5)]";
            assert_equal next 1
        | _ -> assert_bool "one-variable failed" false
    );

    "a-and-b-1" >::
    (fun _ ->
        match a_and_b with 
        | Mature_stream (state, _) ->
            let (substitution, next) = state in
            assert_equal (subst_to_string substitution) 
                        "[Variable(1) -> Value(5), Variable(0) -> Value(7)]";
            assert_equal next 2
        | _ -> assert_bool "a-and-b solution 1 failed" false
    );

    "a-and-b-2" >::
    (fun _ ->
        match a_and_b with 
        | Mature_stream (_, Mature_stream (state, Empty_stream)) ->
            let (substitution, next) = state in
            assert_equal (subst_to_string substitution) 
                        "[Variable(1) -> Value(6), Variable(0) -> Value(7)]";
            assert_equal next 2
        | _ -> assert_bool "a-and-b solution 2 failed" false
    );

    "fives" >::
    (fun _ ->
        match who_cares with 
        | Mature_stream (state, _) ->
            let (substitution, next) = state in
            assert_equal (subst_to_string substitution) "[Variable(0) -> Value(5)]";
            assert_equal next 1
        | _ -> assert_bool "who-cares failed" false
    );


]

let _ = run_test_tt_main tests *)