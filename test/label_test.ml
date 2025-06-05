open Lex_lib.Label

let test_qualified_name (label: t) (expected: string) () =
  Alcotest.(check string) "qualified_name" expected (qualified_name label)

let test_qualified_name_of_law (law: (string * string option) list) (expected: string) () =
  Alcotest.(check string) "qualified_name_of_law" expected (qualified_name_of_law law)

let test_qualified_name_of_level (level: (string * string option) list) (expected: string) () =
  Alcotest.(check string) "qualified_name_of_level" expected (qualified_name_of_level level)

let law1 = [("L1", Some "Law 1")]
let law2 = law1 @ [("L2", Some "Law 2")]
let l1 = { empty with law = law1 }
let l2 = { empty with law = law2 }

let article1 = [("A1", Some "Article 1")]
let article2 = article1 @ [("A2", Some "Article 2")]
let article3 = article2 @ [("A3", Some "Article 3")]

let l3 = { empty with law = law1; article = article1 }
let l4 = { empty with law = law2; article = article2 }
let l5 = { empty with law = law2; article = article3 }
let l6 = { empty with law = law1; article = article2 }
let l7 = { empty with law = law1; article = article3 }

let qualified_name_law_tests = [
  ( "Qualified Name Law Tests", [
      Alcotest.test_case "Qualified Name (Law) 1" `Quick (test_qualified_name_of_law law1 "L1") ;
      Alcotest.test_case "Qualified Name (Law) 2" `Quick (test_qualified_name_of_law law2 "L1")
    ]
  );
]

let qualified_name_of_level_tests = [
  ( "Qualified Name of Level Tests", [
      Alcotest.test_case "Qualified Name (Level) 1" `Quick (test_qualified_name_of_level article1 "(A1)") ;
      Alcotest.test_case "Qualified Name (Level) 2" `Quick (test_qualified_name_of_level article2 "(A1)(A2)") ;
      Alcotest.test_case "Qualified Name (Level) 3" `Quick (test_qualified_name_of_level article3 "(A1)(A2)(A3)") ;
    ]
  );
]

let qualified_name_tests = [
  ( "Qualified Name Tests", [
      Alcotest.test_case "Qualified Name 1" `Quick (test_qualified_name l1 "L1 ") ;
      Alcotest.test_case "Qualified Name 2" `Quick (test_qualified_name l2 "L1 ") ;
      Alcotest.test_case "Qualified Name 3" `Quick (test_qualified_name l3 "L1 A1") ;
      Alcotest.test_case "Qualified Name 4" `Quick (test_qualified_name l4 "L1 A1(A2)") ;
      Alcotest.test_case "Qualified Name 5" `Quick (test_qualified_name l5 "L1 A1(A2)(A3)") ;
      Alcotest.test_case "Qualified Name 6" `Quick (test_qualified_name l6 "L1 A1(A2)") ;
      Alcotest.test_case "Qualified Name 7" `Quick (test_qualified_name l7 "L1 A1(A2)(A3)")
    ]
  );
]

let label_tests = qualified_name_law_tests @
                  qualified_name_of_level_tests @
                  qualified_name_tests