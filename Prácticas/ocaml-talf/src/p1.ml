(*Eduardo Pérez Fraguela, 49674118Y, Grupo 3.3*)

(*Ejercicio 1*)

#load "talf.cma";;
open Auto;;
open Conj;;
open Ergo;;
open Graf;;
open List;;

let config_af cadena (Af (_, _, inicial, _, finales) as a) =
  let rec aux lista  = function

      (Conjunto [], lista_simbolos) ->
          lista

      |(Conjunto actuales, []) ->
          append [(actuales),[]] lista

      |(Conjunto actuales, simbolo :: t) ->
          aux (append [(actuales),simbolo::t] lista) ((epsilon_cierre (avanza simbolo (Conjunto actuales) a) a), t)

  in
      aux [] ((epsilon_cierre (Conjunto [inicial]) a), cadena)
  ;;
(*val config_af : Auto.simbolo List.t -> Auto.af -> (Auto.estado list * Auto.simbolo List.t) List.t = <fun>*)

let rec imprimir_estados = function 
  [] -> ()
  | (Estado e)::l -> print_string "Estado "; print_string e ;print_string " "; imprimir_estados l;;
(*val imprimir_estados : Auto.estado List.t -> unit = <fun>*)

let rec imprimir_traza = function
  [] -> ()
  | (e, c)::l -> imprimir_estados e ;print_string "- Cadena: "; print_endline (string_of_cadena c) ; imprimir_traza l;;
(*val imprimir_traza : (Auto.estado List.t * Auto.simbolo list) List.t -> unit = <fun>*)

let traza_af s a =
  if escaner_af s a then begin (imprimir_traza (config_af s a)); true end else false;;
(*val traza_af : Auto.simbolo List.t -> Auto.af -> bool = <fun>*) 

(*let a = af_of_file "/home/fraguela/Escritorio/Ingeniería Informática/mencion_3/TC/practica/ocaml-talf/data/ejemplo01.af";;*)
(*let b = [Terminal "a"; Terminal "b"; Terminal "b" ; Terminal "a"; Terminal "c"];;*)
(*let b = cadena_of_string "a b b a c";;*)



(*Ejercicio 2*)

let interseccion_estados (Estado e1) (Estado e2) = Estado (e1^e2);;
(*La intersección la uso para los alfabetos de entrada*)
let producto_cartesiano c1 c2 =                                       
  let rec aux acc caux1 caux2 =                             
    match caux1, caux2 with                                             
      Conjunto [], _ -> acc                                    
      |Conjunto (h::t), Conjunto [] -> aux acc (Conjunto t) caux2 
      |Conjunto (h1::t1), Conjunto (h2::t2) -> aux (agregar (h1,h2) acc) caux1 (Conjunto t2)
      in aux conjunto_vacio c1 c2;;

let rec conj_estados c1 = 
  let rec aux acc =  function                                            
      Conjunto [] -> acc                                    
      |Conjunto ((Estado x, Estado y)::t) -> aux (append acc [(Estado (x^y))]) (Conjunto t) 
      in aux [] c1;;
 
let rec interseccion c1 c2 = match c1 with 
  Conjunto [] -> if c2 = (Conjunto []) then Conjunto [] else interseccion c2 c1
  | Conjunto (h::t) -> if pertenece h c2 then 
                      let aux = suprimir h c2 in agregar h (interseccion (Conjunto t) aux)
                      else interseccion (Conjunto t) c2;;

let producto_cartesiano_arcos c1 c2 =                                       
  let rec aux acc caux1 caux2 =                             
    match caux1, caux2 with                                             
      Conjunto [], _ -> acc                                    
      |Conjunto (h::t), Conjunto [] -> aux acc (Conjunto t) caux2 
      |Conjunto (h1::t1), Conjunto (h2::t2) -> aux (agregar (h1,h2) acc) caux1 (Conjunto t2)
      in aux conjunto_vacio c1 c2;;


let rec conj_arcos c1 = 
  let rec aux acc =  function                                            
      Conjunto [] -> acc                                    
      |Conjunto ((Arco_af (Estado x, Estado y, z), Arco_af (Estado x1, Estado y1, z1))::t) -> aux (acc@[Arco_af (Estado (x^x1), Estado (y^y1), z1)]@[Arco_af (Estado (x^x1), Estado (y^y1), z)]) (Conjunto t) 
      in aux [] c1;;

let rec remove_dups lst= match lst with
  | [] -> []
  | h::t -> h::(remove_dups (List.filter (fun x -> x<>h) t));;

let conj_arcos_def c = remove_dups (conj_arcos c);;

let cartesiano_base a1 a2 = match (a1, a2) with
  Af(q1, e1, q01, d1, f1), Af(q2, e2, q02, d2, f2) -> Af(Conjunto (conj_estados (producto_cartesiano q1 q2)), (interseccion e1 e2), (interseccion_estados q01 q02), Conjunto (conj_arcos_def (producto_cartesiano d1 d2)), Conjunto (conj_estados (producto_cartesiano f1 f2)));;
