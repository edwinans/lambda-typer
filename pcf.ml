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

type vartype = Unknown of string | Instance of ptype

and ptype = TVar of vartype ref | Arr of ptype * ptype | N | TList of ptype

and forall = Forall of string list * ptype

type equa = (ptype * ptype) list

type typing_error = Unbound_var of string | Clash of ptype * ptype

exception Type_error of typing_error

let get_head l =
  match l with Empty -> failwith "list is empty" | Cons (x, _) -> x

let get_tail l =
  match l with Empty -> failwith "list is empty" | Cons (_, xs) -> xs

let rec print_string_list l =
  let rec aux = function Empty -> "" | Cons (x, xs) -> x ^ ", " ^ aux xs in
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

and print_type t =
  match t with
  | TVar {contents= Unknown x} ->
      x
  | TVar {contents= Instance t} ->
      print_type t
  | Arr (m, n) ->
      "(" ^ print_type m ^ " -> " ^ print_type n ^ ")"
  | N ->
      "int"
  | TList a ->
      print_type a ^ " list"

let var_counter : int ref = ref 0

let new_var () : string =
  var_counter := !var_counter + 1 ;
  "T" ^ string_of_int !var_counter

let new_unknown () = TVar (ref (Unknown (new_var ())))

(* return all type variables of t*)
let get_vars t =
  let rec aux t acc =
    match t with
    | TVar v -> (
      match !v with
      | Unknown n ->
          if List.mem n acc then acc else n :: acc
      | Instance t ->
          aux t acc )
    | Arr (t1, t2) ->
        let acc = aux t1 acc in
        aux t2 acc
    | N ->
        acc
    | TList t1 ->
        aux t1 acc
  in
  aux t []

let rec remove_all l1 l2 =
  match l1 with
  | [] ->
      []
  | x :: xs ->
      if List.mem x l2 then remove_all xs l2 else x :: remove_all xs l2

let get_free_vars_env (env : (string * forall) list) : string list =
  let rec aux env acc =
    match env with
    | [] ->
        List.sort_uniq String.compare (List.flatten acc)
    | (_, t) :: xs -> (
      match t with
      | Forall (var, t1) ->
          let vars = get_vars t1 in
          let free_vars = remove_all vars var in
          aux xs (free_vars :: acc) )
  in
  aux env []

let get_eq_target eq target =
  match eq with t1, t2 -> if target = t1 then t2 else t1

let type_instance st =
  match st with
  | Forall (gv, t) ->
      let unknowns = List.map (function n -> (n, new_unknown ())) gv in
      let rec instance = function
        | TVar {contents= Unknown n} as t -> (
          try List.assoc n unknowns with Not_found -> t )
        | TVar {contents= Instance t} ->
            instance t
        | N ->
            N
        | TList t ->
            TList (instance t)
        | Arr (t1, t2) ->
            Arr (instance t1, instance t2)
      in
      instance t

let rec generalise (env : (string * forall) list) (t : ptype) : forall =
  let free_vars = get_free_vars_env env in
  let vars = List.filter (fun v -> not (List.mem v free_vars)) (get_vars t) in
  Forall (vars, t)

let occurs n t = List.mem n (get_vars t)

let rec shorten = function
  | TVar vt as tt -> (
    match !vt with
    | Unknown _ ->
        tt
    | Instance (TVar _ as t) ->
        let t2 = shorten t in
        vt := Instance t ;
        t2
    | Instance t ->
        t )
  | t ->
      t

let rec unify_types (t1, t2) =
  let lt1 = shorten t1 and lt2 = shorten t2 in
  match (lt1, lt2) with
  | TVar ({contents= Unknown n} as occn), TVar {contents= Unknown m} ->
      if n = m then () else occn := Instance lt2
  | TVar ({contents= Unknown n} as occn), _ ->
      if occurs n lt2 then raise (Type_error (Clash (lt1, lt2)))
      else occn := Instance lt2
  | _, TVar {contents= Unknown n} ->
      unify_types (lt2, lt1)
  | N, N ->
      ()
  | TList t1, TList t2 ->
      unify_types (t1, t2)
  | Arr (t1, t2), Arr (t3, t4) ->
      unify_types (t1, t3) ;
      unify_types (t2, t4)
  | _ ->
      raise (Type_error (Clash (lt1, lt2)))

let alpha = TVar (ref (Unknown "alpha"))

and beta = TVar (ref (Unknown "beta"))

let rec type_expr gamma =
  let rec type_rec expri =
    match expri with
    | Int n ->
        N
    | Var s ->
        let t =
          try List.assoc s gamma
          with Not_found -> raise (Type_error (Unbound_var s))
        in
        type_instance t
    | Hd l ->
        let l_type = Forall (["alpha"], Arr (TList alpha, alpha)) in
        let t1 = type_instance l_type
        and t2 = type_rec l
        and u = new_unknown () in
        unify_types (t1, Arr (t2, u)) ;
        u
    | Tail l ->
        let l_type = Forall (["alpha"], Arr (TList alpha, TList alpha)) in
        let t1 = type_instance l_type and t2 = type_rec l in
        let u = new_unknown () in
        unify_types (t1, Arr (t2, u)) ;
        u
    | Add (e1, e2) ->
        let t = Arr (N, Arr (N, N)) and t1 = type_rec e1 and t2 = type_rec e2 in
        unify_types (t1, N) ;
        unify_types (t2, N) ;
        N
    | Sub (e1, e2) ->
        let t = Arr (N, Arr (N, N)) and t1 = type_rec e1 and t2 = type_rec e2 in
        unify_types (t1, N) ;
        unify_types (t2, N) ;
        N
    | List Empty ->
        TList (new_unknown ())
    | List (Cons (e1, e2)) ->
        let t1 = type_rec e1 and t2 = type_rec (List e2) in
        unify_types (TList t1, t2) ;
        t2
    | If_Zero (e1, e2, e3) ->
        let t1 = type_rec e1 and t2 = type_rec e2 and t3 = type_rec e3 in
        unify_types (t1, N) ;
        unify_types (t2, t3) ;
        t2
    | If_Empty (e1, e2, e3) ->
        let target = Forall (["alpha"], TList alpha) in
        let t1 = type_rec e1 and t2 = type_rec e2 and t3 = type_rec e3 in
        let u1 = type_instance target in
        unify_types (t1, u1) ;
        unify_types (t2, t3) ;
        t2
    | App (e1, e2) ->
        let t1 = type_rec e1 and t2 = type_rec e2 in
        let u = new_unknown () in
        unify_types (t1, Arr (t2, u)) ;
        u
    | Abs (s, e) ->
        let t = new_unknown () in
        let new_env = (s, Forall ([], t)) :: gamma in
        Arr (t, type_expr new_env e)
    | Let (s, e1, e2) ->
        let t1 = type_rec e1 in
        let tg = generalise gamma t1 in
        type_expr ((s, tg) :: gamma) e2
    | Let_Rec (s, e1, e2) ->
        let u = new_unknown () in
        let new_env = (s, Forall ([], u)) :: gamma in
        let t1 = type_expr (new_env @ gamma) e1 in
        let tg = generalise new_env t1 in
        type_expr ((s, tg) :: gamma) e2
  in
  type_rec

let main () =
  print_endline
    (pretty_printer (Tail (List (Cons (Int 3, Cons (Int 4, Empty))))))
