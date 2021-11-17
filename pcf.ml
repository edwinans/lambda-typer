type 'a plist = Empty | Cons of 'a * 'a plist

type pterm =
  | Var of string
  | App of pterm * pterm
  | Abs of string * pterm
  | Int of int
  | Add of pterm * pterm
  | Sub of pterm * pterm
  | List of pterm plist
  | Hd of pterm 
  | Tail of pterm 
  | If_Empty of pterm * pterm * pterm
  | If_Zero of pterm * pterm * pterm
  | Let of string * pterm * pterm
  | Let_Rec of string * pterm * pterm

type ptype =
  | TVar of string
  | Arr of ptype * ptype
  | N
  | TList of ptype
  | Forall of string plist * ptype

type typing_error = Unbound_var of string | Clash of ptype * ptype

exception Type_error of typing_error

let get_head l =
  match l with Empty -> failwith "list is empty" | Cons (x, _) -> x

let get_tail l =
  match l with Empty -> failwith "list is empty" | Cons (_, xs) -> xs
let rec print_string_list l= 
  let rec aux = function
      | Empty ->
          ""
      | Cons (x, xs) ->
          x ^ ", " ^ aux xs
    in
    "[" ^ aux l ^ "]"

let rec print_pterm_list l =
  let rec aux = function
    | Empty ->
        ""
    | Cons (x, xs) ->
        pretty_printer x ^ ", " ^ aux xs
  in
  "[" ^ aux l ^ "]"

and pretty_printer term =
  match term with
  | Var s ->
      s
  | App (m, n) ->
      "(" ^ pretty_printer m ^ " " ^ pretty_printer n ^ ")"
  | Abs (x, m) ->
      "(fun " ^ x ^ " -> " ^ pretty_printer m ^ ")"
  | Int n ->
      string_of_int n
  | Add (a, b) ->
      pretty_printer a ^ " + " ^ pretty_printer b
  | Sub (a, b) ->
      pretty_printer a ^ " - " ^ pretty_printer b
  | List l ->
      print_pterm_list l
  | Hd l ->
      "Hd(" ^ pretty_printer l ^ ")"
  | Tail l ->
      "Tail(" ^ pretty_printer l ^ ")"
  | If_Empty (l, e1, e2) ->
      "if " ^ pretty_printer l ^ " == empty then " ^ pretty_printer e1
      ^ pretty_printer e2
  | If_Zero (n, e1, e2) ->
      "if " ^ pretty_printer n ^ " == 0 then " ^ pretty_printer e1
      ^ pretty_printer e2
  | Let (x, e1, e2) ->
      "let " ^ x ^ " = " ^ pretty_printer e1 ^ " in " ^ pretty_printer e2
  | Let_Rec (x, e1, e2) ->
      "let rec " ^ x ^ " = " ^ pretty_printer e1 ^ " in " ^ pretty_printer e2

and print_type t = match t with
  | TVar x ->
      x
  | Arr (m, n) ->
      "(" ^ print_type m ^ " -> " ^ print_type n ^ ")"
  | N -> "int"
  | TList (a) -> print_type a ^ " list"
  | Forall (l, p) -> "Forall " ^ (print_string_list l) ^ "." ^ print_type p

let var_counter : int ref = ref 0

let new_var () : string =
  var_counter := !var_counter + 1 ;
  "T" ^ string_of_int !var_counter



let main () = 
  begin
  print_endline (
    pretty_printer  (
      Tail(List(Cons(Int(3), Cons(Int(4), Empty))))
    )
    )
  end