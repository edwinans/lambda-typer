type pterm = Var of string | App of pterm * pterm | Abs of string * pterm
            | N of int | Add of pterm * pterm | Sub of pterm * pterm 
            | Empty
            | List of pterm * pterm 
            | Hd of pterm 
            | Tail of pterm
            | Cons of pterm * pterm  
            | IF_Empty of pterm * pterm
            | IF_Zero of pterm * pterm 
            | Let of string * pterm * pterm

type ptype = TVar of string | Arr of ptype * ptype | N | L of ptype 

