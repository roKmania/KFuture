require "kool-typed-dynamic.k"

module FUTURE-SYNTAX
  imports KOOL-TYPED-DYNAMIC-SYNTAX
  
  syntax Exp ::= // ... | 
                 Exp "!" Id "(" Exps ")" [avoid, strict(1)]
               | Guard

  syntax Id ::= "get" [token]
  syntax Guard ::= "wait" | Id "?"
  syntax Type ::= "!" Type
  syntax Stmt ::= "await" Exp ";"
                | Block "[]" Block [right]
                | Block "||" Block [right]                
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
                          <fId> 0 </fId>
                          <task-guards> .Set </task-guards>
                          <waiting-task-conf> .Bag </waiting-task-conf>
                        </waiting-task> 
                      </waiting-tasks>
                      <active-task>
                        <futureId> 0 </futureId>
                        <taskState> active </taskState>
                        <blocked-threads>
                          <blocked-thread multiplicity="*">
                            <guard> .K </guard>
                            <blocked-thread-conf> .Bag </blocked-thread-conf>
                          </blocked-thread> 
                        </blocked-threads>
                        <threads color="orange">
                           <thread multiplicity="*" color="yellow">
                              <k color="green"> ($PGM:Stmts ~> execute) </k>
  
                              <br/>
                              <control color="cyan">
                                <crntClass> Object </crntClass>
                                <fstack color="blue"> .List </fstack>
                                <xstack color="purple"> .List </xstack>
                                <return color="LimeGreen"> void </return>  // KOOL
                              </control>
                              <br/>
                              <env color="violet"> .Map </env>
                              <holds color="black"> .Map </holds>
                              <id color="pink"> 0 </id>
                           </thread>
                        </threads>
                        <br/>
                        <busy color="cyan">.Set </busy>
                        <terminated color="red"> .Set </terminated>
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
       <futureId> 0 => F </futureId>
       <blocked-threads> . </blocked-threads>
       <threads>
         .
         =>
         <thread>...
           <k> lookupThis(<envStack> ES </envStack>, Class, Method) ( Vs ) </k>
         ...</thread>
       </threads>
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
  
  rule <k> super . Method:Id(Vs:Vals) => (superCall(Id, Class) ! Method(Vs)).get
      ...</k>
      <crntClass> Class </crntClass>
      <location> Id:Int </location>

  syntax Val ::= superCall(Int,Id)

/*
  - a super call creates a new future and "returns" the identifier
    of the new future 
*/
  rule <k> superCall(X:Int, Class) ! Method:Id(Vs:Vals)
        => future(F) ...</k>
       <className> Class </className>
       <extends> Class':Id </extends>
       (. => <future>... <fid> F </fid> <oid> X </oid> <mClass> Class' </mClass>
                         <method> Method </method> <arguments> Vs </arguments>
             ...</future>)
       <nextFutureId> F:Int => F +Int 1 </nextFutureId>


/*
  The rules for blocking/unblocking tasks:
*/

  // the case when the future is not done
  rule (<thread> <k> future(Id).get ~> K </k> T:Bag </thread> => . ) 
       (. => <blocked-thread> <guard> future(Id).get ~> K </guard> 
                              <blocked-thread-conf> T </blocked-thread-conf>
             </blocked-thread>)
       <fid> Id </fid>
       <state> S:State </state>
       requires S =/=K completed [futureBlock]

  // the case when the future is done
  rule (. => <thread> <k> future(Id).get ~> K </k> T:Bag </thread>) 
       (<blocked-thread> <guard> future(Id).get ~> K </guard> 
                         <blocked-thread-conf> T </blocked-thread-conf>
        </blocked-thread> => .)
       <taskState> _ => active </taskState>
       <fid> Id </fid>
       <state> completed </state>

/*
  The rule that transforms an active task into an waiting task
*/
  rule <futureId> F => 0 </futureId>
       <blocked-threads> BT:Bag => . </blocked-threads>
       <taskState> active </taskState>
       <threads> . </threads>
       (. => <waiting-task> <fId> F </fId>
                            <task-guards> getGuards(BT) </task-guards> 
                            <waiting-task-conf> BT </waiting-task-conf> 
             </waiting-task>)
       //<token> .K => 0 </token>
      requires notBool(BT ==Bag .Bag)
 
/*
  The rule transforming a waiting task into an active one. 
*/
  rule <blocked-threads> . => BT </blocked-threads>
       <threads> . </threads>
       <taskState> _ => sleeping </taskState>
       <futureId> 0 => F </futureId>
       (<waiting-task> <fId> F </fId> 
                       <task-guards>... SetItem(future(Id).get) ...</task-guards> 
                       <waiting-task-conf> BT </waiting-task-conf> 
        </waiting-task> => .)
       <fid> Id </fid>
       <state> completed </state>
    [futureUnblock]

/*
  The new semantics of the return statement:
*/

  rule
    <futureId> Id => 0 </futureId> 
    <blocked-threads> . </blocked-threads>
    (   <threads>   // force single thread returns
          <thread>... 
             <k> return V:Val; ...</k> 
          ...</thread>
         </threads> 
     => <threads> . </threads>
    )
/*  Alternative semantics:  Just end returning thread; other can continue
    (<thread>... <k> return V:Val; ...</k> ...</thread> => .)
*/
    <future>... <fid> Id </fid>
                <state> active => completed </state>
                (. => <result> V </result>)
    ...</future>


  syntax Val ::= "nothing"

  rule
    <futureId> Id => 0 </futureId>
    <threads> . </threads>
    <blocked-threads> . </blocked-threads>
    <future>... <fid> Id </fid>
                <state> active => completed </state>
                (. => <result> nothing </result>)
    ...</future>



/*
  The semantics of the get metod:
*/

  rule <k> future(Id).get => V ...</k>
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
  Additional field lookup semantics for lvalue:
*/
  rule <k> lvalue(object(Id:Int, _, Class:Id) . X
                  =>
                  lookupThis(<envStack> ES </envStack>, Class, X))
       ...</k>
       <location> Id </location>
       <envStack> ES:List </envStack>
  [structural]
     


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


  rule <k> future(Id).get => throw V; ...</k>
       <fid> Id </fid>
       <result> exception(V:Val) </result>

/*  Spawn
*/
  rule <thread>...
         <k> spawn S => !T:Int ...</k>
         <env> Env </env>
       ...</thread>
       (. => <thread>...
               <k> S </k>
               <env> Env </env>
               <id> !T </id>
             ...</thread>)


/*
  Auxiliary stuff:
*/
  rule .Bag ==Bag .Bag => true
  rule (_:BagItem _:Bag ==Bag .Bag) => false
  rule (.Bag ==Bag _:BagItem _:Bag) => false
  rule I:BagItem B:Bag ==Bag I B':Bag => B ==Bag B'

  syntax Set ::= getGuards(Bag) [function]

  rule getGuards(<blocked-thread>... <guard> future(Id).get ...</guard>
                 ...</blocked-thread> B:Bag) => getGuards(B) SetItem(future(Id).get)
  rule getGuards(.Bag) => .Set

endmodule
