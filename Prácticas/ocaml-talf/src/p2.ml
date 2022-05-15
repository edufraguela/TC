(*Eduardo Pérez Fraguela, 49674118Y, Grupo 3.3*)

(*Ejercicio 1*)

#load "talf.cma";;
open Auto;;
open Conj;;
open Ergo;;
open Graf;;
open List;;

let obtener_estados = Conjunto [Estado "0"; Estado "1"; Estado "2"];;
(*val obtener_estados : Auto.estado Conj.conjunto = Conjunto [Estado "0"; Estado "1"; Estado "2"]*)


let obtener_terminales =
  let rec aux lista_terminales indice = function
      (Gic (Conjunto([]), cn, e, cz)) -> Conjunto (List.rev lista_terminales)
      |(Gic (Conjunto (h::t), cn, e, cz)) ->
      aux  ((Terminal (string_of_int indice))::lista_terminales) (indice+1) (Gic(Conjunto (t), cn, e, cz))
    
  in aux [] 0;;
(*val obtener_terminales : Auto.gic -> Auto.simbolo Conj.conjunto = <fun>*)


let obtener_no_terminales = function
  Gic(nt,t,r,f) -> nt;;
(*val obtener_no_terminales : Auto.gic -> Auto.simbolo Conj.conjunto = <fun>*) 


let arco_inicial = Arco_ap (Estado "0", Estado "1", Terminal "", No_terminal "", [No_terminal "S"; No_terminal ""]);;
(*val arco_inicial : Auto.arco_ap = Arco_ap (Estado "0", Estado "1", Terminal "", No_terminal "", [No_terminal "S"; No_terminal ""])*)


let arco_final = Arco_ap (Estado "1", Estado "2", Terminal "", No_terminal "", [No_terminal ""]);;
(*val arco_final : Auto.arco_ap = Arco_ap (Estado "1", Estado "2", Terminal "", No_terminal "", [No_terminal ""])*)


let arcos_vaciar_pila (Conjunto terminales) =
  let rec aux arcos = function
    [] -> Conjunto arcos
    | h::t -> aux ((Arco_ap (Estado "1", Estado "1", h, h, []))::arcos) t
  in aux [] terminales;; 
(*val arcos_vaciar_pila : Auto.simbolo Conj.conjunto -> Auto.arco_ap Conj.conjunto = <fun>*)


let arcos_llenar_pila (Conjunto reglas) =
  let rec aux arcos = function
    [] -> Conjunto (List.rev (arco_final::arcos))
    | Regla_gic(nt, l)::t -> aux ((Arco_ap (Estado "1", Estado "1", Terminal "", nt, l))::arcos) t
  in aux [arco_inicial] reglas;;
(*val arcos_llenar_pila : Auto.regla_gic Conj.conjunto -> Auto.arco_ap Conj.conjunto = <fun>*)


let ap_of_gic  = function
  Gic(nt, t, r, f) -> Ap (obtener_estados, t, union nt (Conjunto [No_terminal ""]), 
  Estado "0", union (arcos_llenar_pila r) (arcos_vaciar_pila t), No_terminal "", Conjunto [Estado "2"]);;
(*val ap_of_gic : Auto.gic -> Auto.ap = <fun>*)

(*let a = gic_of_file "/home/fraguela/Escritorio/Ingeniería Informática/mencion_3/TC/practica/ocaml-talf/data/ejemplo01.gic";;*)
(*ap_of_gic a;;*)
(*dibuja_ap(ap_of_gic a);;*)

    
(*Ejercicio 2*)
let imprimir_estado = function
   Estado x ->  print_string x;;
(*val imprimir_estado : Auto.estado -> unit = <fun>*)


let imprimir_cadena c = List.iter (function Terminal x -> print_string x | No_terminal x -> print_string x) c;;
(*let imprimir_cadena c = List.iter (function Terminal x -> print_string x | No_terminal x -> print_string x) c;;*)


let imprimir_conf x y z =
    imprimir_estado x;
    print_string " ";
    imprimir_cadena y;
    print_string " [";
    imprimir_cadena z;
    print_string "]";;
(*val imprimir_conf : Auto.estado -> Auto.simbolo list -> Auto.simbolo list -> unit = <fun>*)


let imprimir_confs x y z nx ny nz =
    imprimir_conf x y z;
    print_string " -> ";
    imprimir_conf nx ny nz;
    print_newline ();;
(*val imprimir_confs : Auto.estado -> Auto.simbolo list -> Auto.simbolo list -> Auto.estado -> Auto.simbolo list -> Auto.simbolo list -> unit = <fun>*)


let imprimir_cond estado nuevo_estado cadena nueva_cadena nueva_pila_conf entrada =
    if (estado <> nuevo_estado) 
    || (cadena <> nueva_cadena)
    || ((cadena <> []) && (entrada = hd cadena))
    || (hd nueva_pila_conf = hd cadena) then true
    else false;;
(*val imprimir_cond : 'a -> 'a -> 'b List.t -> 'b List.t -> 'b list -> 'b -> bool = <fun>*)


exception No_encaja;;


let encaja_ap (estado, cadena, pila_conf) (Arco_ap (origen, destino, entrada, cima, pila_arco)) =
  let
     nuevo_estado =
        if estado = origen then
           destino
        else
           raise No_encaja
  and
     nueva_cadena =
        if entrada = Terminal "" then
           cadena
        else
           if (cadena <> []) && (entrada = hd cadena) then
              tl cadena
           else
              raise No_encaja
  and
     nueva_pila_conf =
        if cima = Terminal "" then
           pila_arco @ pila_conf
        else
           if (pila_conf <> []) && (cima = hd pila_conf) then
              pila_arco @ (tl pila_conf)
           else
              raise No_encaja
  in
       if imprimir_cond estado nuevo_estado cadena nueva_cadena nueva_pila_conf entrada then
           imprimir_confs estado cadena pila_conf nuevo_estado nueva_cadena nueva_pila_conf;
       (nuevo_estado, nueva_cadena, nueva_pila_conf);;
(*val encaja_ap : Auto.estado * Auto.simbolo List.t * Auto.simbolo List.t -> Auto.arco_ap -> Auto.estado * Auto.simbolo List.t * Auto.simbolo list = <fun>*)


let es_conf_final finales = function
  (estado, [], _) -> pertenece estado finales
  | _ -> false;;
(*val es_conf_final : 'a Conj.conjunto -> 'a * 'b List.t * 'c -> bool = <fun>*)
  

let config_ap cadena (Ap (_, _, _, inicial, Conjunto delta, zeta, finales)) =
    let rec aux = function
        ([], [], _) -> false
      | ([], l, _) -> aux (l, [], delta)
      | (_::cfs, l, []) -> aux (cfs, l, delta)
      | (cf::cfs, l, a::arcos) ->
            try
              let
                  ncf = encaja_ap cf a
              in
                  (es_conf_final finales ncf) || (aux (cf::cfs, ncf::l, arcos))
            with
              No_encaja -> aux (cf::cfs, l, arcos)
    in
      aux ([(inicial, cadena, [zeta])], [], delta)
    ;;
(*val config_ap : Auto.simbolo List.t -> Auto.ap -> bool = <fun>*)

(*let g = gic_of_string "S; a b c; S; S -> a S a | b S b | c;";;*)
(*let ap = ap_of_gic g;;*)
(*Esta da true -> let c = cadena_of_string "a b c b a";;*)
(*config_ap c ap;;*)
(*Esta da false -> let b = cadena_of_string "a b b a c";;*)


