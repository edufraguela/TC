(*Eduardo Pérez Fraguela, 49674118Y, Grupo 3.3*)

(*#################Ejercicio 1#################*)
let rec mapdoble f1 f2  = function
    [] -> []
    | h::[] -> f1 h::[]
    | h1::h2::t -> f1 h1::f2 h2::mapdoble f1 f2 t;; 
(*val mapdoble : ('a -> 'b) -> ('a -> 'b) -> 'a list -> 'b list = <fun>*)

mapdoble (function x -> x*2) (function x -> "x") [1;2;3;4;5];;
(*Error: This expression has type string but an expression was expected of type int*)
(*Se produce un error debido a que en la primera función se indica que el tipo es 
int ya que se realiza la operación "*2", esto obliga a que la segunda función también
sea un int cuando es una cadena.*)

let y = function x -> 5 in mapdoble y;;
(*- : ('_weak1 -> int) -> '_weak1 list -> int list = <fun>*)

(*#################Ejercicio 2#################*)
let rec primero_que_cumple f = function
    [] -> raise Not_found 
    | h::t -> if (f h) then h else primero_que_cumple f t;;
(*val primero_que_cumple : ('a -> bool) -> 'a list -> 'a = <fun>*)

let existe f l = match (primero_que_cumple f l) with
    exception Not_found -> false
    | _ -> true;;
(*val existe : ('a -> bool) -> 'a list -> bool = <fun>*)

let asociado l x = match (primero_que_cumple (function i -> x = fst i) l) with
    exception Not_found -> raise Not_found
    |(x, y) -> y;;
(*val asociado : ('a * 'b) list -> 'a -> 'b = <fun>*)

(*#################Ejercicio 3#################*)
type 'a arbol_binario=
    Empty
    | Node of 'a * 'a arbol_binario * 'a arbol_binario;;

let t = Node (3, Node(2, Empty, Empty), Node(5, Node(4, Empty, Empty), Node(1, Empty, Empty)));;

let rec in_orden = function 
    Empty -> []
    | Node (r, Empty, Empty) -> [r]
    | Node (r, i, d) -> in_orden i @ [r] @ in_orden d;;
(*val in_orden : 'a arbol_binario -> 'a list = <fun>*)

let rec pre_orden = function
    Empty -> []
    | Node (r, Empty, Empty) -> [r]
    | Node (r, i, d) -> [r] @ pre_orden i @ pre_orden d;;
(*val pre_orden : 'a arbol_binario -> 'a list = <fun>*)

let rec post_orden = function
    Empty -> []
    | Node (r, Empty, Empty) -> [r]
    | Node (r, i, d) -> post_orden i @ post_orden d @ [r];;
(*val post_orden : 'a arbol_binario -> 'a list = <fun>*)

let anchura arbol = 
    let rec aux p s = match p with
        [] -> List.rev s
        | Empty::t -> aux t s 
        | Node(r, i, d)::t -> aux (t@[i]@[d])(r::s)
    in aux [arbol] [];;
(*val anchura : 'a arbol_binario -> 'a list = <fun>*)


(*#################Ejercicio 4#################*)
(*Propiedades de conjuntos:
    1.- No hay repetidos
    2.- No importa el orden
*)

type 'a conjunto = Conjunto of 'a list;;

let conjunto_vacio = Conjunto [];; 

let rec pertenece x = function
    Conjunto [] -> false
    |Conjunto (h::t) -> if x=h then true else pertenece x (Conjunto t);;
(*val pertenece : 'a -> 'a conjunto -> bool = <fun>*)

let rec agregar x = function 
    Conjunto [] -> Conjunto [x]
    | Conjunto l -> if pertenece x (Conjunto l) then Conjunto l else Conjunto (x::l);;
(*val agregar : 'a -> 'a conjunto -> 'a conjunto = <fun>*)

let rec conjunto_of_list = function 
    [] -> Conjunto []
    | h::[] -> Conjunto (h::[])
    | h1::h2::t -> if h1 = h2 then conjunto_of_list (h2::t) else agregar h1 (conjunto_of_list(h2::t));;
(*val conjunto_of_list : 'a list -> 'a conjunto = <fun>*)

let rec suprimir x = function 
    Conjunto [] -> Conjunto []
    | Conjunto (h::t) -> if x = h then suprimir x (Conjunto t) else agregar h (suprimir x (Conjunto t));;
(*val suprimir : 'a -> 'a conjunto -> 'a conjunto = <fun>*)

let rec cardinal = function
    Conjunto [] -> 0
    | Conjunto (h::t) -> 1 + cardinal (Conjunto t);;
(*val cardinal : 'a conjunto -> int = <fun>*)

let rec union (Conjunto c1) = function 
    Conjunto c2 -> conjunto_of_list(c1@c2);;
(*val union : 'a conjunto -> 'a conjunto -> 'a conjunto = <fun>*)

let rec interseccion c1 c2 = match c1 with 
    Conjunto [] -> if c2 = (Conjunto []) then Conjunto [] else interseccion c2 c1
    | Conjunto (h::t) -> if pertenece h c2 then 
                        let aux = suprimir h c2 in agregar h (interseccion (Conjunto t) aux)
                        else interseccion (Conjunto t) c2;;
(*val interseccion : 'a conjunto -> 'a conjunto -> 'a conjunto = <fun>*)

let rec diferencia c = function 
    Conjunto [] -> c
    | Conjunto (h::t) -> diferencia (suprimir h c) (Conjunto t);;
(*val diferencia : 'a conjunto -> 'a conjunto -> 'a conjunto = <fun>*)

let rec incluido c1 c2 = match c1,c2 with 
    Conjunto [], _ -> true
    | (Conjunto (h::t)), (Conjunto c) -> if pertenece h (Conjunto c) then incluido (Conjunto t) (Conjunto c) else false;;
(*val incluido : 'a conjunto -> 'a conjunto -> bool = <fun>*)

let igual c1 c2 = match c1, c2 with 
    Conjunto [], Conjunto [] -> true
    | c1, c2 -> if ((diferencia c1 c2) = Conjunto []) && ((diferencia c2 c1) = Conjunto [])
        then true
        else false;; 
(*val igual : 'a conjunto -> 'a conjunto -> bool = <fun>*)

let producto_cartesiano c1 c2 =                                       
    let rec aux acc caux1 caux2 =                             
      match caux1, caux2 with                                             
        Conjunto [], _ -> acc                                    
        |Conjunto (h::t), Conjunto [] -> aux acc (Conjunto t) caux2 
        |Conjunto (h1::t1), Conjunto (h2::t2) -> aux (agregar (h1,h2) acc) caux1 (Conjunto t2)
        in aux conjunto_vacio c1 c2;;
(*val producto_cartesiano : 'a conjunto -> 'b conjunto -> ('a * 'b) conjunto = <fun>*)

let list_of_conjunto = function 
    Conjunto l -> l;;
(*val list_of_conjunto : 'a conjunto -> 'a list = <fun>*)