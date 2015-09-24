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
                    <future multiplicity="*">       // future
                      <fid> .K </fid>                 // future identifier
                      <oid> .K </oid>                 // object identifier
                      <closure> .K </closure>         // function closure
                      <arguments> .K </arguments>     // function arguments
                      <result multiplicity="?"> .K </result> // computed result
                      <state> sleeping </state>       // state of the future
                    </future>
                  </futures>
                  <objects>
                    <object multiplicity="*">      // object
                      <location> 0 </location>        // object identifier
                      <baseClass> Object </baseClass> // creation class
                      <envStack> .List </envStack>    // stack of class envs
                      <waiting-tasks>                 // suspended tasks
                        <waiting-task multiplicity="*">
                          <fId> 0 </fId>                 // future identifier
                          <task-guards> .Set </task-guards>  // set of guards
                          <waiting-task-conf> .Bag </waiting-task-conf>
                        </waiting-task> 
                      </waiting-tasks>
                      <active-task>                  // current task
                        <futureId> 0 </futureId>       // future identifier
                        <taskState> active </taskState>// state = active/sleeping
                        <blocked-threads>              // suspended threads
                          <blocked-thread multiplicity="*">
                            <guard> .K </guard>          // guard to wake thread
                            <blocked-thread-conf> .Bag </blocked-thread-conf>
                          </blocked-thread> 
                        </blocked-threads>
                        <threads color="orange">      // running threads
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
  An object value consists  of a triple (Id, MainClass, CurrentClass), where:
  * Id is an integer identifying the object
  * MainClass is the class the object was created with (using new)
    used to checking whether the object can be casted to some type
  * CurrentClass is the current class of the object (obtained through casting)
    used for dynamically type checking
*/

  syntax ObjectVal ::= object(Int,Id,Id)
  syntax Val ::= ObjectVal

/* 
  Redefinition of the semantics for new.
  - an instance of the class is created (<object> cell) and
    an unique identifier is assigned to it
  - then the "$clinit" special method is called
    as an ususal method to do class initialization
  - once that is done, the constructor is called
  - Finally, the result is the identifier of the new object
  - Both class initialization and constructor are blocking to ensure
    the object reference is not exposed during initialization.
*/
  syntax Id ::= "$clinit" 

  rule <k> new Class:Id(Vs:Vals)
           => object(Id,Class,Class) . $clinit(.Exps); ~> object(Id,Class,Class).Class(Vs); ~> object(Id,Class,Class) ...</k>
       <nextObjectId> Id:Int => Id +Int 1 </nextObjectId>
       (. => <object>...
                <location> Id </location>
                <baseClass> Class </baseClass>
                <active-task>... <futureId> -1 </futureId> ...</active-task>
             ...</object>)


/*
  The redefinition of the semantics for this:
  - this returns a reference to the current object.
*/

  rule <k> this => object(Id,BClass,Class) ...</k>
       <location> Id:Int </location>
       <crntClass> Class:Id </crntClass>
       <baseClass> BClass:Id </baseClass>

/*
  The semantics of a future call.  A future call creates a new future
  and "returns" the identifier of the new future.
  Elements needed:
  * the object identifier (where the method is to be called)
  * the class from which the method should be called
    - currently used mainly for super
    - could also be useful to implement other method lookup mechanisms
  * the name of the method to be called
  * the (already evaluated) arguments to be passed to the method.
*/

  // the arguments are strict such that they are evaluated first
  context _:ObjectVal ! Method:Id(HOLE)

  rule <k> object(OId,Class,_) ! Method:Id(Vs:Vals)
        => future(F) ...</k>
       (. => <future>...
               <fid> F </fid> <oid> OId </oid>
               <closure> lookupMethod(Class,Method) </closure>
               <arguments> Vs </arguments>
             ...</future>)
       <nextFutureId> F:Int => F +Int 1 </nextFutureId>

  // future identifiers
  syntax Val ::= future(Int)
  syntax KItem ::= lookupMethod(Id,Id)

/* Looking up the location of a future method by name
  * The method is looked up in the envStack of the object,
    starting from specified class
  * can be done in parallel with any existing tasks
*/
  rule <future>
         <fid> F:Int </fid>
         <oid> Id:Int </oid>
          <closure>
             lookupMethod(Class,Method)
          => lookupThis(<envStack> ES </envStack>, Class, Method)
          </closure>
         <arguments> Vs:Vals </arguments>
         <state> sleeping </state>
       </future>
       <location> Id </location>
       <envStack> ES:List </envStack>

/* 
  The activation of a sleeping future
  * a future can only be activated if there is no active state
    - signaled by futureId holding -1
  * performCall does the actual method invocation
*/

  rule <future> 
         <fid> F:Int </fid>
         <oid> Id:Int </oid>
         <closure> Closure </closure>
         <arguments> Vs:Vals </arguments>
         <state> sleeping => active </state>
       </future>
       <location> Id </location>
       <envStack> ES:List </envStack>
       <futureId> -1 => F </futureId>
       <threads>
         .
         =>
         <thread>...  <k> performCall(Closure, Vs) </k> ...</thread>
       </threads>
    [futureStart]

/*
  Performing a local call:
  * Parameters are bound to arguments, then the body is executed
  * the current reference class is updated to the class of the method
*/
  syntax KItem ::= performCall(K, Vals) [strict(1)]

  rule <k> performCall(methodClosure(_,Class,OL,Ps,S), Vs:Vals)
           => mkDecls(Ps,Vs) S
       </k>
       <crntClass> _ => Class </crntClass>


/*  Semantics for the class initializer. See definition of KOOL for create.
*/
  rule <k> performCall($clinitClosure, _) => create(Class) </k>
       <baseClass> Class:Id </baseClass>
       <envStack> .List => ListItem((Object, <env>.Map</env>)) </envStack>

/*
  Method calls desugar into (blocking) future invocations
*/

  rule O:ObjectVal . Method:Id(Vs:Vals) 
    => (O ! Method(Vs)).get
  
/*
  A super call desugars into a normal call using a fake object
  having the super class as a base.
*/

  rule <k> super . Method:Id(Vs:Vals)
        => object(Id, Class', Class') . Method(Vs)
       ...</k>
      <crntClass> Class </crntClass>
      <location> Id:Int </location>
      <className> Class </className>
      <extends> Class':Id </extends>

/* Function calls desugar into future calls on the current object
*/
  rule <k>  methodClosure(Type,Class,OL,Ps,S) (Vs:Vals)
        => future(F).get ...</k>
       <location> OId </location>
       (. => <future>...
               <fid> F </fid> <oid> OId </oid>
               <closure> methodClosure(Type,Class,OL,Ps,S) </closure>
               <arguments> Vs </arguments>
             ...</future>)
       <nextFutureId> F:Int => F +Int 1 </nextFutureId>

/*
  The rules for blocking/unblocking tasks:
*/

  // A thread blocks while waiting for a future to complete
  rule (<thread> <k> future(Id).get ~> K </k> T:Bag </thread> => . ) 
       (. => <blocked-thread> <guard> future(Id).get ~> K </guard> 
                              <blocked-thread-conf> T </blocked-thread-conf>
             </blocked-thread>)
       <fid> Id </fid>
       <state> S:State </state>
       requires S =/=K completed [futureBlock]

  // A thread unblocks when the future is done
  rule (. => <thread> <k> future(Id).get ~> K </k> T:Bag </thread>) 
       (<blocked-thread> <guard> future(Id).get ~> K </guard> 
                         <blocked-thread-conf> T </blocked-thread-conf>
        </blocked-thread> => .)
       <taskState> _ => active </taskState>
       <fid> Id </fid>
       <state> completed </state>

/*
  The rule that transforms an active task into an waiting task
  * If all threads are blocked, we suspend the task.
  * We use -1 for futureId to signal that there is no active task
  * task-guards is a collection of all guards from the blocked threads
*/
  rule <futureId> F => -1 </futureId>
       <blocked-threads> BT:Bag => . </blocked-threads>
       <taskState> active </taskState>
       <threads> . </threads>
       (. => <waiting-task> <fId> F </fId>
                            <task-guards> getGuards(BT) </task-guards> 
                            <waiting-task-conf> BT </waiting-task-conf> 
             </waiting-task>)
      requires notBool(BT ==Bag .Bag)
 
/*
  The rule transforming a waiting task into an active one. 
  * When any of the task guards is completed, we can awake a task
    if there is no active task.
*/
  rule <blocked-threads> . => BT </blocked-threads>
       <taskState> _ => sleeping </taskState>
       <futureId> -1 => F </futureId>
       (<waiting-task> <fId> F </fId> 
                       <task-guards>... SetItem(future(Id).get) ...</task-guards> 
                       <waiting-task-conf> BT </waiting-task-conf> 
        </waiting-task> => .)
       <fid> Id </fid>
       <state> completed </state>
    [futureUnblock]

/*
  The new semantics of the return statement:
  * When the only thread of the task returns, we deactivate the task
    and set the returned value as the result of the corresponding future.
*/

  rule
    <futureId> Id => -1 </futureId> 
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


/* If the active task completes without returning, set the result value
   to nothing and signal future completion.
*/
  syntax Val ::= "nothing"

  rule
    <futureId> Id => -1 </futureId>
    <threads> . </threads>
    <blocked-threads> . </blocked-threads>
    <future>... <fid> Id </fid>
                <state> active => completed </state>
                (. => <result> nothing </result>)
    ...</future>


/*
  The semantics of future get.
  The requires clause is due to exceptions; see below.
*/

  rule <k> future(Id).get => V ...</k>
       <fid> Id </fid>
       <result> V:Val </result>
    requires isExceptionVal(V) =/=K true

/*
  Field lookup is allowed only from the current object 
  and is done relative to the object's current reference class
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
     


/*  Lookup helper.  Finds the reference class in the environment stack,
    then invokes lookupMember.
*/

  syntax KItem ::= lookupThis(EnvStackCellSort,K,Id)  [function]
  rule lookupThis(_, _, $clinit) => $clinitClosure
  syntax Val ::= "$clinitClosure"
  rule lookupThis(<envStack>ListItem((Class':Id,_)) EStack </envStack>, Class:Id, X) 
    => lookupThis(<envStack>EStack</envStack>, Class, X)
    requires Class =/=K Class'
  rule lookupThis(<envStack>ListItem((Class:Id,B:Bag)) EStack </envStack>, Class, X)
    => lookupMember(<envStack>ListItem((Class:Id,B:Bag)) EStack</envStack>, X)




/*
  TypeOf returns the current reference class.
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

/* Uncaught Exception.
   If an exception is not caught in the current task, it is returned as
   an exceptional value.  When get is used on an exceptional value, the
   exception is thrown again.
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
