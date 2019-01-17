namespace GuardedCommands.Backend
// Michael R. Hansen 05-01-2016, 04-01-2018
// This file is obtained by an adaption of the file MicroC/Comp.fs by Peter Sestoft
open System
open Machine

open GuardedCommands.Frontend.AST
module CodeGeneration =


(* A global variable has an absolute address, a local one has an offset: *)
    type Var = 
        | GloVar of int                   (* absolute address in stack           *)
        | LocVar of int                   (* address relative to bottom of frame *)
    
    (* The variable environment keeps track of global and local variables, and 
    keeps track of next available offset for local variables *)
    
    type varEnv = Map<string, Var*Typ> * int
    
    (* The function environment maps function name to label and parameter decs *)
    
    type ParamDecs = (Typ * string) list
    type funEnv = Map<string, label * Typ option * ParamDecs>

    (* Bind declared parameters in env: *)
    
    let bindParam (env, fdepth) dec  = 
        match dec with 
        | VarDec (typ, x) -> (Map.add x (LocVar fdepth, typ) env , fdepth+1)
        | _ -> failwith ("Parameters in a function can't be a function ")
    
    let bindParams paras ((env, fdepth) : varEnv) : varEnv = 
        List.fold bindParam (env, fdepth) paras
    
    (* ------------------------------------------------------------------- *)
    
    /// CE vEnv fEnv e gives the code for an expression e on the basis of a variable and a function environment
    let rec CE vEnv fEnv = function
        | N n          -> [CSTI n]
        | B b          -> [CSTI (if b then 1 else 0)]
        | Access acc   -> CA vEnv fEnv acc @ [LDI] 
        | Apply("!", [e]) -> CE vEnv fEnv e @  [NOT]
        | Apply("-", [e]) -> CE vEnv fEnv e @  [CSTI 0; SWAP; SUB]
        | Addr acc        -> CA vEnv fEnv acc
        | Apply("&&",[b1;b2]) ->    let labend   = newLabel()
                                    let labfalse = newLabel()
                                    CE vEnv fEnv b1 @ [IFZERO labfalse] @ CE vEnv fEnv b2
                                    @ [GOTO labend; Label labfalse; CSTI 0; Label labend]
        
        | Apply(o,[e1;e2]) when List.exists (fun x -> o=x) ["+"; "*"; "=";"-"; "<>"; "<"; ">="; ">"; "<="]
             -> let ins = match o with
                          | "+"  -> [ADD]
                          | "-"  -> [SUB]
                          | "*"  -> [MUL]
                          | "="  -> [EQ] 
                          | "<>"  -> [EQ; NOT]
                          | "<"   -> [LT]
                          | ">="  -> [LT; NOT]
                          | ">"   -> [SWAP; LT]
                          | "<="  -> [SWAP; LT; NOT]
                          | _    -> failwith "CE: this case is not possible"
                CE vEnv fEnv e1 @ CE vEnv fEnv e2 @ ins 
        | Apply(f, es) -> callfun f es vEnv fEnv
        | _            -> failwith "CE: not supported yet"
    
    
    /// CA vEnv fEnv acc gives the code for an access acc on the basis of a variable and a function environment
    and CA vEnv fEnv = function 
        | AVar x         -> match Map.find x (fst vEnv) with
                               | (GloVar addr,_) -> [CSTI addr]
                               | (LocVar addr,_) -> [GETBP; CSTI addr; ADD]
        | AIndex(acc, e) -> CA vEnv fEnv acc
                            @ [LDI] @ CE vEnv fEnv e @ [ADD]
        | ADeref e       -> CE vEnv fEnv e
    
    (* Peter Sestoft MicroC *)
    and cExprs es varEnv funEnv : instr list = 
        List.concat(List.map (fun e -> CE varEnv funEnv e) es)
    
    (* Peter Sestoft MicroC *)
    and callfun f es vEnv fEnv : instr list =
        let (labf, tyOpt, paramdecs) = Map.find f fEnv
        let argc = List.length es
        if argc = List.length paramdecs then
          cExprs es vEnv fEnv @ [CALL(argc, labf)]
        else
          raise (Failure (f + ": parameter/argument mismatch"))
    
    (* Bind declared variable in env and generate code to allocate it: *)   
    let allocate (kind : int -> Var) (typ, x) (vEnv : varEnv)  =
        let (env, fdepth) = vEnv 
        match typ with
            | ATyp (ATyp _, _) -> 
                raise (Failure "allocate: array of arrays not permitted")
            | ATyp (t, Some i) ->
                let newEnv = (Map.add x (kind (fdepth+i), typ) env, fdepth+i+1)
                let code = [INCSP i; GETSP; CSTI (i-1); SUB]
                (newEnv, code)
            | _ -> 
                let newEnv = (Map.add x (kind fdepth, typ) env, fdepth+1)
                let code = [INCSP 1]
                (newEnv, code)
    
    
    
    
    /// CS vEnv fEnv s gives the code for a statement s on the basis of a variable and a function environment                          
    let rec CS vEnv fEnv isFunction = function
        | PrintLn e        -> CE vEnv fEnv e @ [PRINTI; INCSP -1] 
    
        | Ass(acc,e)       -> CA vEnv fEnv acc @ CE vEnv fEnv e @ [STI; INCSP -1]
    
        | Block([],stms)   -> CSs vEnv fEnv isFunction stms
        
        | Block(dcls, stms) -> let varScope = match isFunction  with 
                                              | true -> LocVar
                                              | false -> GloVar
                               let rec loop decList vEnv' = (*Inspiration from Peter Sestoft MicroC*)
                                   match decList with
                                   | [] -> (vEnv', [])
                                   | dec :: decTail ->
                                     let varDec = match dec with | VarDec(t,s) -> (t,s)
                                     let (vEnv1, code1) = allocate varScope varDec vEnv'
                                     let (vEnv2, code) = loop decTail vEnv1
                                     (vEnv2, code1 @ code)
                               let (vEnv1, codeDec) = loop dcls vEnv
                               codeDec @ CSs vEnv1 fEnv isFunction stms @ [INCSP (snd vEnv - snd vEnv1)]
        
        | Alt (GC (gcl))   -> let labend = newLabel()
                              List.fold (fun il (e, stms) ->
                                 let subend = newLabel()
                                 il @ CE vEnv fEnv e @ [IFZERO subend] @
                                 CSs vEnv fEnv isFunction stms
                                 @ [GOTO labend] @ [Label subend] @ [Label labend] 
                              ) [] gcl
             
        | Do (GC (gcl))   -> let labelstart = newLabel()
                             let labend = newLabel()
                             [Label labelstart] @
                             List.fold (fun il (e, stms) ->
                                let subend = newLabel()
                                il @ CE vEnv fEnv e @ [IFZERO subend] @
                                ( CSs vEnv fEnv isFunction stms @ [GOTO labelstart] @ [Label subend]
                                ) 
                             ) [] gcl @ [Label labend] 
        | Return None -> 
            [RET (snd vEnv - 1)]
        | Return (Some e) -> 
            CE vEnv fEnv e @ [RET (snd vEnv)]      
        | Call(s, es) -> callfun s es vEnv fEnv @ [INCSP -1]
        | _               -> failwith "CS: this statement is not supported yet"
    
    and CSs vEnv fEnv isFunction stms = List.collect (CS vEnv fEnv isFunction) stms 
    
    
    
    (* ------------------------------------------------------------------- *)
    
    (* Build environments for global variables and functions *)
    
    let makeGlobalEnvs decs = 
        let rec addv decs vEnv fEnv = 
            match decs with 
            | []         -> (vEnv, fEnv, [])
            | dec::decr  -> 
                match dec with
                | VarDec (typ, var) -> let (vEnv1, code1) = allocate GloVar (typ, var) vEnv
                                       let (vEnv2, fEnv2, code2) = addv decr vEnv1 fEnv
                                       (vEnv2, fEnv2, code1 @ code2)
                | FunDec (tyOpt, f, xs, body) -> addv decr vEnv (Map.add f (newLabel(), tyOpt, xs) fEnv) //Idea from Peter Sestoft MicroC implementation
    
    
        addv decs (Map.empty, 0) Map.empty
    
    
    
    /// CP prog gives the code for a program prog
    let CP (P(decs,stms)) = 
        let _ = resetLabels ()
        let ((gvM,_) as gvEnv, fEnv, initCode) = makeGlobalEnvs decs
        let compilefun (tyOpt, f, xs, stm) =
            let (labf, _, paras) = Map.find f fEnv
            let (envf, fdepthf) = bindParams paras (gvM, 0)
            let code = CS (envf, fdepthf) fEnv true stm
            [Label labf] @ code @ [RET (List.length paras-1)]
        let functions = 
                    List.choose (function
                                    | FunDec (tyOpt, f, decList, stm) 
                                                -> Some(compilefun (tyOpt, f, decList, stm))
                                    | VarDec _  -> None)
                                decs
        initCode @ CSs gvEnv fEnv false stms @ [STOP] @ List.concat functions
