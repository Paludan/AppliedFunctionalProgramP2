namespace GuardedCommands.Frontend
// Michael R. Hansen 06-01-2016 , 04-01-2018

open System
open Machine
open GuardedCommands.Frontend.AST

module TypeCheck = 
   open Parser
   open System.Diagnostics

/// tcE gtenv ltenv e gives the type for expression e on the basis of type environments gtenv and ltenv
/// for global and local variables 
   let rec tcE gtenv ltenv = function                            
         | N _              -> ITyp   
         | B _              -> BTyp   
         | Access acc       -> tcA gtenv ltenv acc     
                   
         | Apply(f,[e]) when List.exists (fun x ->  x=f) ["-";"!"]  
                            -> tcMonadic gtenv ltenv f e        

         | Apply(f,[e1;e2]) when List.exists (fun x ->  x=f) ["+";"*"; "="; "&&"; "-"; "<"; ">"; "<>"; "<="; ">="; "||"]        
                            -> tcDyadic gtenv ltenv f e1 e2   

         | Apply(f,es)    -> tcNaryFunction gtenv ltenv f es

         | Addr acc       -> PTyp (tcA gtenv ltenv acc)

         | _                -> failwith "tcE: not supported yet"

   and tcMonadic gtenv ltenv f e = match (f, tcE gtenv ltenv e) with
                                   | ("-", ITyp) -> ITyp
                                   | ("!", BTyp) -> BTyp
                                   | _           -> failwith "illegal/illtyped monadic expression" 
   
   and tcDyadic gtenv ltenv f e1 e2 = match (f, tcE gtenv ltenv e1, tcE gtenv ltenv e2) with
                                      | (o, ITyp, ITyp) when List.exists (fun x ->  x=o) ["+";"*"; "-"]  -> ITyp
                                      | (o, ITyp, ITyp) when List.exists (fun x ->  x=o) ["="; "<"; ">"; "<>"; "<="; ">="] -> BTyp
                                      | (o, BTyp, BTyp) when List.exists (fun x ->  x=o) ["&&";"="; "||"]     -> BTyp 
                                      | _                      -> failwith("illegal/illtyped dyadic expression: " + f)

   and tcNaryFunction gtenv ltenv f es =   let ftype = if (Map.containsKey f gtenv)
                                                       then Map.find f gtenv
                                                       else failwith ("no declaration for : " + f)
                                           match ftype with 
                                                | FTyp (tl, typeo) -> if (List.length tl = List.length es)                  
                                                                      then if(List.fold(fun tces (a,b) -> tces && (checkType gtenv ltenv a b))  true (List.zip tl es))
                                                                           then match typeo with 
                                                                                    | Some t -> t
                                                                                    | None -> failwith ("No return from function " + f)
                                                                           else failwith ("Parameter types can't be matched. Can't call function " + f)
                                                                      else failwith ("Because of different parameter number. Can't call function " + f)
                                                | _                -> failwith (f + "is not a function")
       
                                          

                                                            
   
                                        //failwith "type check: functions not supported yet"
 
   and tcNaryProcedure gtenv ltenv f es = let ftype = if (Map.containsKey f gtenv)
                                                      then Map.find f gtenv
                                                      else failwith ("no declaration for procedure: " + f)
                                          match ftype with 
                                                | FTyp (tl, typeo) -> if (List.length tl = List.length es)                  
                                                                      then if(List.fold(fun tces (a,b) -> tces && (checkType gtenv ltenv a b))  true (List.zip tl es))
                                                                           then match typeo with 
                                                                                    | None -> ()
                                                                                    | Some _ -> failwith ("Wrong return type for procedure " + f)
                                                                           else failwith ("Parameter types can't be matched. Can't call procedure " + f)
                                                                      else failwith ("Because of different parameter number. Can't call procedure " + f)
                                                | _                -> failwith (f + "is not a procedure")
                                          //failwith "type check: procedures not supported yet"
   
   and checkType gtenv ltenv typ e = 
        match typ with
            | ATyp (t, into) -> match into with
                                    | None -> match tcE gtenv ltenv e with
                                                | ATyp (t1, _ ) -> t = t1
                                                | _ -> false
                                    | _ -> failwith "Can define the size of array when it is a parameter of a function or procedure"
            | _ -> typ = tcE gtenv ltenv e

/// tcA gtenv ltenv e gives the type for access acc on the basis of type environments gtenv and ltenv
/// for global and local variables 
   and tcA gtenv ltenv = 
         function 
         | AVar x         -> match Map.tryFind x ltenv with
                             | None   -> match Map.tryFind x gtenv with
                                         | None   -> failwith ("no declaration for : " + x)
                                         | Some t -> t
                             | Some t -> t            
         | AIndex(acc, e) -> if tcE gtenv ltenv e = ITyp 
                             then let atyp= tcA gtenv ltenv acc
                                  match atyp with
                                    | ATyp(t, into) -> 
                                        match into with
                                        | None -> t
                                        | Some num-> 
                                            match e with 
                                            | N n -> if ((n >= 0) && (n < num))
                                                        then t
                                                        else failwith "Index is not a valid number"
                                            | Apply ("-", [N n]) -> if (n > 0)
                                                                    then failwith "Index is not a valid number"
                                                                    else failwith ""
                                            | _ ->   t
                                    | _ -> failwith ("It's not a array")
                              else failwith "Index must be an integer"
                                          
                             
  
                            //failwith "tcA: array indexing not supported yes"
         | ADeref e       -> match (tcE gtenv ltenv e) with
                                | PTyp typ -> typ
                                | _ -> failwith "It's not a address"
                                //failwith "tcA: pointer dereferencing not supported yes"
 

/// tcS gtenv ltenv retOpt s checks the well-typeness of a statement s on the basis of type environments gtenv and ltenv
/// for global and local variables and the possible type of return expressions 
   and tcS gtenv ltenv = function                           
                         | PrintLn e -> ignore(tcE gtenv ltenv e)
                         | Ass(acc,e) -> if tcA gtenv ltenv acc = tcE gtenv ltenv e 
                                         then ()
                                         else failwith "illtyped assignment"                                
                         | Return(expo) -> match Map.find "function" ltenv with
                                            |FTyp (tpyl, topt) -> let typeo = 
                                                                        match expo with 
                                                                        | Some t -> Some (tcE gtenv ltenv t)
                                                                        | None -> None
                                                                  if (typeo = topt)
                                                                  then ()
                                                                  else failwith ("Return type is not correct")
                                            | _  -> failwith ("It's not a function")
                                            
                         | Block(decs,stms) -> let newltenv = tcGDecs ltenv decs 
                                               List.iter (tcS gtenv newltenv) stms
                         | Do (g)         -> tcGC gtenv ltenv g
                         | Alt (g)        -> tcGC gtenv ltenv g
                         | Call (p, es)   -> tcNaryProcedure gtenv ltenv p es
                         | _              -> failwith "tcS: this statement is not supported yet"


   and tcGDec gtenv = function  
                      | VarDec(t,s)               -> Map.add s t gtenv
                      | FunDec(topt,f, decs, stm) -> let namel = List.map getNameD decs
                                                     if (Set.count (Set.ofList namel) = List.length namel)
                                                     then //failwith("")
                                                          let typ = FTyp(List.map getTypD decs, topt)
                                                          let newgtenv =Map.add f typ gtenv
                                                          if topt <> None
                                                          then (tcS newgtenv (Map.add "function" typ (tcGDecs Map.empty decs)) stm) |>ignore
                                                               if (checkReturn stm) = false 
                                                               then failwith "Function doesn't return"
                                                          newgtenv
                                                     else failwith ("Parameter names in a function should be different")
                                                     
    and checkReturn = function
              | Return e  -> true
              | Alt (GC (gcl)) -> List.exists (fun stm -> checkReturn stm) (List.fold (fun stl (e,stms)-> stl@stms) [] gcl)
              | Do (GC (gcl))-> List.exists (fun stm -> checkReturn stm) (List.fold (fun stl (e,stms)-> stl@stms) [] gcl)   
              | Block (decs,stms) -> List.exists (fun stm -> checkReturn stm) stms
              | _ -> false

    and getNameD = function
                    | VarDec(t,s)               -> s
                    | FunDec(topt,f, decs, stm) -> failwith ("Function can't be a parameter of function") //f

   and getTypD = function
                    | VarDec(t,s)               -> t
                    | FunDec(topt,f, decs, stm) -> failwith ("Function can't be a parameter of function") //FTyp(List.map getTypD decs, topt)
                                                
   and tcGDecs gtenv = function
                       | dec::decs -> tcGDecs (tcGDec gtenv dec) decs
                       | _         -> gtenv
                       
   and tcGC gtenv ltenv = function 
                        | GC ( gcl ) -> List.iter (fun (e, stms) ->
                                                if (tcE gtenv ltenv e = BTyp)
                                                then List.iter (tcS gtenv ltenv) stms 
                                                else failwith "Illtyped GC expression"
                                             ) gcl
    
/// tcP prog checks the well-typeness of a program prog
   and tcP(P(decs, stms)) = let gtenv = tcGDecs Map.empty decs
                            List.iter (tcS gtenv Map.empty) stms