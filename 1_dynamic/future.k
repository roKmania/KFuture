require "kool-typed-dynamic.k"

module FUTURE-SYNTAX
  imports KOOL-TYPED-DYNAMIC-SYNTAX
  
  syntax Exp ::= // ... | 
                 Exp "!" Id "(" Exps ")" [avoid, strict(1)]
               | Guard

  syntax Id ::= "get" [token]
  syntax Guard ::= "wait" | Exp "?" [strict]
  syntax Type ::= "!" Type
  syntax Stmt ::= "await" Exp ";"
endmodule

module FUTURE
  imports FUTURE-SYNTAX
  imports KOOL-TYPED-DYNAMIC

  syntax State ::= "sleeping" | "active" | "completed"

  configuration <T color="red">
                  <futures>
                    <future multiplicity="*">
                      <fid> .K </fid>
                      <oid> .K </oid>
                      <mClass> .K </mClass>
                      <method> .K </method>
                      <arguments> .K </arguments>
                      <result multiplicity="?"> .K </result>
                      <state> sleeping </state>
                    </future>
                  </futures>
                  <objects>
                    <object multiplicity="*">
                      <location> 0 </location>
                      <baseClass> Object </baseClass>
                      <envStack> .List </envStack>
                      <token> .K </token>
                      <waiting-tasks>
                        <waiting-task multiplicity="*">
                          <guard multiplicity="?"> .Set </guard>
                          <waiting-k> .K </waiting-k>
                          <waiting-task-conf> .Bag </waiting-task-conf>
                        </waiting-task> 
                      </waiting-tasks>
                      <active-task>
                        <futureId> 0 </futureId>
                        <k color="green"> ($PGM:Stmts ~> execute) </k>
                        <br/>
                        <control color="cyan">
                           <crntClass> Object </crntClass>
                           <xstack color="purple"> .List </xstack>
                        </control>
                        <br/>
                        <env color="violet"> .Map </env>
                      </active-task>
                      <nextLoc color="gray"> 0 </nextLoc>
                      <store color="white"> .Map </store>
                    </object>
                  </objects>
                  <nextObjectId> 1 </nextObjectId>
                  <nextFutureId> 1 </nextFutureId>
                  <in color="magenta" stream="stdin"> .List </in>
                  <out color="brown" stream="stdout"> .List </out>
                  <br/>
                  <classes color="Fuchsia">        // KOOL
                     <class multiplicity="*" color="Fuchsia">
                        <className color="Fuchsia"> Main </className>
                        <extends color="Fuchsia"> Object </extends>
                        <declarations color="Fuchsia"> .K </declarations>
                     </class>
                  </classes>
                </T>


/*
  Object identifiers (references).
*/

  syntax ObjectVal ::= object(Int,Id,Id)
  syntax Val ::= ObjectVal

/* 
  Redefinition of the semantics for new.
  - an instance of the class is created and
    an unique identifier is assigned to it
  - then the constructor is called as an ususal method
  - the result is the identifier of the new object
*/
  syntax Id ::= "$clinit" 

  rule <k> new Class:Id(Vs:Vals)
           => (object(Id,Class,Class) ! $clinit(.Exps)).get; ~> (object(Id,Class,Class) ! Class(Vs)).get; ~> object(Id,Class,Class) ...</k>
       <nextObjectId> Id:Int => Id +Int 1 </nextObjectId>
       (. => <object>...
                <k> . </k>
                <location> Id </location>
                <baseClass> Class </baseClass>
             ...</object>)


/*
  The redefinition of the semantics for this:
*/

  rule <k> this => object(Id,BClass,Class) ...</k>
       <location> Id:Int </location>
       <crntClass> Class:Id </crntClass>
       <baseClass> BClass:Id </baseClass>

/*
  The semantics of the method call with futures.
*/

  // the arguments are strict such that they are evaluated first
  context _:ObjectVal ! Method:Id(HOLE)

  // future identifiers
  syntax Val ::= future(Int)

/*
  - a method call creates a new futures and "returns" the identifier
    of the new future 
*/
  rule <k> object(X:Int,_,_) ! Method:Id(Vs:Vals)
        => future(F) ...</k>
       (. => <future>... <fid> F </fid> <oid> X </oid>
                         <method> Method </method> <arguments> Vs </arguments>
             ...</future>)
       <nextFutureId> F:Int => F +Int 1 </nextFutureId>

/* 
  The activation of a sleeping future
*/

  rule <location> Id </location>
       <envStack> ES:List </envStack>
       (<active-task>... <futureId> 0 </futureId> <k> . </k> ...</active-task>
        =>
        <active-task>...
           <futureId> F </futureId>
           <k> lookupThis(<envStack> ES </envStack>, Class, Method) ( Vs ) </k>
        ...</active-task>
       )
       <future> 
         <fid> F:Int </fid>
         <oid> Id:Int </oid>
         <mClass> Class </mClass>
         <method> Method:Id </method>
         <arguments> Vs:Vals </arguments>
         <state> sleeping => active </state>
       </future>
    [futureStart]

/*
  The semantics of a local call (???)
*/

  rule <k> methodClosure(_->T,Class,OL,Ps,S)(Vs:Vals) 
           => mkDecls(Ps,Vs) S
       </k>
       <crntClass> _ => Class </crntClass>


  rule <k> lookupMember(<envStack> .List </envStack>,$clinit)(.Exps) => create(Class) </k>
       <baseClass> Class:Id </baseClass>
       <envStack> .List => ListItem((Object, <env>.Map</env>)) </envStack>

/*
  The semantics of a complete method call
*/

  rule O:ObjectVal . Method:Id(Vs:Vals) 
    => (O ! Method(Vs)).get
  
/*
  - a super call creates a new future and "returns" the identifier
    of the new future 
*/

   rule <k> super . Method:Id(Vs:Vals) => future(F).get ...</k>
      <crntClass> Class </crntClass>
      <location> Id:Int </location>
       <className> Class </className>
       <extends> Class':Id </extends>
       (. => <future>... <fid> F </fid> <oid> Id </oid> <mClass> Class' </mClass>
                         <method> Method </method> <arguments> Vs </arguments>
             ...</future>)
       <nextFutureId> F:Int => F +Int 1 </nextFutureId>

/*
  The rules for blocking/unblocking tasks:
*/

  // the case when the future is not done
  rule ( <active-task> Task  
           <k> waiting(<guard> Guards:Set </guard>) ~> K </k> 
         </active-task>
        =>
         <active-task>... <k> . </k> ...</active-task> ) 
       (. => <waiting-task> 
               <guard> Guards </guard> 
               <waiting-k> K </waiting-k>               
               <waiting-task-conf> Task </waiting-task-conf>
             </waiting-task>)

  // the case when the future is done
  rule (<active-task>... <futureId> 0 </futureId> <k> . </k> ...</active-task>
        =>
        <active-task> Task <k> K </k> </active-task>
       )
       (<waiting-task> <waiting-k> K </waiting-k>
                       <waiting-task-conf> Task </waiting-task-conf>
        </waiting-task> => .)
  [futureUnblock]

/* Basic semantics for await
*/
  rule await(E1 && E2); => await(E1); ~> await(E2);
  rule await(true); => .
  context waiting(<guard> _:Set SetItem(HOLE ?) </guard>)
  rule await(E ?); => waiting(<guard> SetItem(E ?)</guard>)
  rule await(wait); => waiting(<guard> SetItem(wait)</guard>)
  rule await(E1 || E2); => waiting(<guard> SetItem(E1) SetItem(E2)</guard>)

  syntax KItem ::= waiting(Bag)
  rule <guard>... SetItem(true) ...</guard> => .
  rule <guard>... SetItem(E1 || E2) => SetItem(E1) SetItem(E2) ...</guard>
  rule waiting(.Bag) => .

  rule (<guard>... SetItem(future(Id) ?) ...</guard> => .)
       <fid> Id </fid>
       <state> completed </state> 

  rule <waiting-task>...
         <guard>... SetItem(wait) ...</guard> => . 
       ...</waiting-task>

/* Semantics for Future ? 
*/

  rule <k> future(Id) ? => State ==K completed ...</k>
       <fid> Id </fid>
       <state> State </state>

/*
  The new semantics of the return statement:
*/

  rule ( <active-task>...
            <futureId> Id </futureId>
            <k> return V:Val; ...</k> 
         ...</active-task>
        => 
         <active-task>... <k> . </k> ...</active-task>) 
       <future>... <fid> Id </fid>
         <state> active => completed </state>
         (. => <result> V </result>)
       ...</future>

  syntax Val ::= "nothing"

  rule ( <active-task>...
           <futureId> Id </futureId>
           <k> . </k> 
         ...</active-task>
        =>
         <active-task>... <k> . </k> ...</active-task> ) 
       <future>...
         <fid> Id </fid>
         <state> active => completed </state>
         (. => <result> nothing </result>)
       ...</future>

/*
  The semantics of the get metod:
*/

  rule future(Id).get => await(future(Id) ?); ~> getResult(Id)

  syntax KItem ::= getResult(Int)
 
  rule <k> getResult(Id) => V ...</k>
       <fid> Id </fid>
       <result> V:Val </result>
    requires isExceptionVal(V) =/=K true
/*
  Field lookup is allowed only from the current object 
  and is done relative to the object's class
*/
  rule <k> object(Id:Int, _, Class:Id) . X
                  =>
                  lookupThis(<envStack> ES </envStack>, Class, X)
       ...</k>
       <location> Id </location>
       <envStack> ES:List </envStack>
  [structural]


/* Super Field lookup
*/
  rule <k> super . X => lookupThis(<envStack> ES </envStack>, Class', X) 
       ...</k>
       <envStack> ES:List </envStack>
       <crntClass> Class:Id </crntClass>
       <className> Class </className>
       <extends> Class':Id </extends>

/*
  Duplicate field lookup semantics for lvalue:
*/
  rule <k> lvalue(object(Id:Int, _, Class:Id) . X
                  =>
                  lookupThis(<envStack> ES </envStack>, Class, X))
       ...</k>
       <location> Id </location>
       <envStack> ES:List </envStack>
  [structural]
     
  rule <k> lvalue(super . X 
                  => lookupThis(<envStack> ES </envStack>, Class', X)) 
       ...</k>
       <envStack> ES:List </envStack>
       <crntClass> Class:Id </crntClass>
       <className> Class </className>
       <extends> Class':Id </extends>



/*  Lookup Method
*/

  syntax KItem ::= lookupThis(EnvStackCellSort,K,Id)  [function]
  rule lookupThis(B,.,Id:Id) => lookupMember(B, Id)
  rule lookupThis(<envStack>ListItem((Class':Id,_)) EStack </envStack>, Class:Id, X) 
    => lookupThis(<envStack>EStack</envStack>, Class, X)
    requires Class =/=K Class'
  rule lookupThis(<envStack>ListItem((Class:Id,B:Bag)) EStack </envStack>, Class, X)
    => lookupMember(<envStack>ListItem((Class:Id,B:Bag)) EStack</envStack>, X)

/*
  TypeOf
*/
  rule typeOf(object(_,_,Class:Id)) => Class

/* Cast
*/
  rule (C:Id) object(Obj, BClass:Id, C':Id)
    => object(Obj, BClass, C') instanceOf C ~> true?
       ~> object(Obj, BClass, C)


/* instanceOf
*/
  rule object(Obj, BClass, _) instanceOf C => subtype(BClass, C)


/* Unsafe Cast
*/
  rule unsafeCast(object(Id, BClass:Id, _), Class:Id)
    => object(Id, BClass, Class)

/* Uncaught Exception
*/

  syntax ExceptionVal ::= exception(Val)
  syntax Val ::= ExceptionVal

  rule <k> throw V:Val; => return exception(V); ...</k>
       <xstack> . </xstack>


  rule <k> getResult(Id) => throw V; ...</k>
       <fid> Id </fid>
       <result> exception(V:Val) </result>

/* Hack for future types
*/
  rule subtype( typeOf( future(_)), ! _) => true
  rule unsafeCast(future(Id), ! _) => future(Id)

endmodule
