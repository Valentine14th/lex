(* Dummy tests *)

let test_example () =
  Alcotest.(check int) "example test" 4 (2 + 2)

let test_2 () =
  Alcotest.(check int) "example test" 3 (1 + 2)

let example_tests = [ ("Example Suite", [
      Alcotest.test_case "Example Test" `Quick test_example;
      Alcotest.test_case "Example Test 2" `Quick test_2;
    ];)
  ]

(* util.ml test cases*)

let test_int_list_equality l1 l2 expected () =
  let open Lex_lib.Util in
  Alcotest.(check bool) "Int List Equality" expected (equal_elements_int_lists l1 l2)

let util_tests = [
  ("Util Int List Equality Tests", [
    Alcotest.test_case "Int List Equality 1" `Quick (test_int_list_equality [1; 2; 3] [1; 2; 3] true);
    Alcotest.test_case "Int List Equality 2" `Quick (test_int_list_equality [1; 2; 3] [3; 2; 1] true);
    Alcotest.test_case "Int List Equality 2" `Quick (test_int_list_equality [1; 1; 2; 3] [3; 2; 1] false);
    Alcotest.test_case "Int List Equality 2" `Quick (test_int_list_equality [] [3; 2; 1] false);
    Alcotest.test_case "Int List Equality 2" `Quick (test_int_list_equality [] [] true);
  ];)
]


(* Combine all test suites *)

let all_tests =
  example_tests @
  util_tests


(* Run the tests *)

let () = Alcotest.run "Lex Tests" all_tests