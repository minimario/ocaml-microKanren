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

let rec appendo2 = fun l s out ->
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
                        (fun sc ->
                            Immature_stream (fun () -> (appendo2 (Variable d) s (Variable res) sc))
                        )
                        (equals (TermList [Variable a; Variable res]) out))
                    )
                ))
            )
        ))
    )

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

let call_appendo2 = (
    (call_fresh (fun q ->
        (call_fresh (fun l ->
            (call_fresh (fun s ->
                (call_fresh (fun out ->
                    (conj
                        (appendo2 (Variable l) (Variable s) (Variable out))
                        (equals (TermList [Variable l; Variable s; Variable out]) (Variable q))
                    )
                ))
            ))
        ))
    )) empty_state
)

let rec relo = fun x ->
    (call_fresh (fun x1 -> (call_fresh (fun x2 ->
        (conj 
            (equals x (TermList [Variable x1; Variable x2]))
            (disj
                (equals (Variable x1) (Variable x2))
                (fun sc ->
                    Immature_stream (fun () -> (relo x sc))    
                )
            )
        )
    ))))

let many_non_ans = 
    call_fresh (fun x -> 
        (disj 
            (relo (TermList [Value 5; Value 6]))
            (equals (Variable x) (Value 3))
        )
    ) empty_state

let rec term_to_str term = match term with 
    | Variable v -> "Variable(" ^ string_of_int v ^ ")"
    | Value v -> "Value(" ^ string_of_int v ^ ")"
    | TermList tl -> 
        let terms = List.map ~f:term_to_str tl in
            "TermList [" ^ (String.concat ~sep:", " terms) ^ "]"

let subst_to_string subst = 
    let terms = List.map ~f:(fun (variable, term) ->
        "Variable(" ^ string_of_int variable ^ ") -> " ^ term_to_str term
    ) subst in 
    "[" ^ (String.concat ~sep:", " terms) ^ "]"

let rec find_next_mature stream = match stream with 
    | Empty_stream -> Empty_stream
    | Mature_stream (state, stream) -> Mature_stream (state, stream)
    | Immature_stream is -> find_next_mature (is ())

let tests = "Test Suite for Microkanren" >::: [
    "one-variable" >::
    (fun _ ->
        match one_variable with 
        | Mature_stream ((substitution, next), Empty_stream) ->
            assert_equal (subst_to_string substitution) "[Variable(0) -> Value(5)]";
            assert_equal next 1
        | _ -> assert_bool "one-variable failed" false
    );

    "a-and-b-1" >::
    (fun _ ->
        match a_and_b with 
        | Mature_stream ((substitution, next), _) ->
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
        | Mature_stream ((substitution, next), _) ->
            assert_equal (subst_to_string substitution) "[Variable(0) -> Value(5)]";
            assert_equal next 1
        | _ -> assert_bool "who-cares failed" false
    );

    "appendo" >::
    (fun _ ->
        match call_appendo with 
        | Mature_stream ((substitution, next), next_stream) ->
            assert_equal (subst_to_string substitution)
                         "[Variable(0) -> TermList [Variable(1), Variable(2), Variable(3)], Variable(2) -> Variable(3), Variable(1) -> TermList []]";
            assert_equal next 4;

            (match find_next_mature next_stream with 
            | Mature_stream ((substitution', next'), _) ->
                assert_equal (subst_to_string substitution') 
                             "[Variable(0) -> TermList [Variable(1), Variable(2), Variable(3)], Variable(2) -> Variable(6), Variable(5) -> TermList [], Variable(3) -> TermList [Variable(4), Variable(6)], Variable(1) -> TermList [Variable(4), Variable(5)]]";
                assert_equal next' 7;
            | _ -> assert_bool "appendo failed on second stream" false)
        | _ -> assert_bool "appendo failed on first result" false
    );

    "appendo2" >::
    (fun _ ->
        match call_appendo2 with 
        | Mature_stream ((substitution, next), next_stream) ->
            assert_equal (subst_to_string substitution)
                         "[Variable(0) -> TermList [Variable(1), Variable(2), Variable(3)], Variable(2) -> Variable(3), Variable(1) -> TermList []]";
            assert_equal next 4;

            (match find_next_mature next_stream with 
            | Mature_stream ((substitution', next'), _) ->
                assert_equal (subst_to_string substitution') 
                             "[Variable(0) -> TermList [Variable(1), Variable(2), Variable(3)], Variable(3) -> TermList [Variable(4), Variable(6)], Variable(2) -> Variable(6), Variable(5) -> TermList [], Variable(1) -> TermList [Variable(4), Variable(5)]]";
                assert_equal next' 7;
            | _ -> assert_bool "appendo failed on second stream" false)
        | _ -> assert_bool "appendo failed on first result" false
    );

    "many non-ans" >::
    (fun _ ->
        match many_non_ans with 
        | Mature_stream ((substitution, next), _) ->
            assert_equal (subst_to_string substitution) "[Variable(0) -> Value(3)]";
            assert_equal next 1
        | _ -> assert_bool "many non-ans failed" false
    );
]

let _ = run_test_tt_main tests