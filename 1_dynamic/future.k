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
                      <method> .K </method>
                      <arguments> .K </arguments>
                      <result multiplicity="?"> .K </result>
                      <state> sleeping </state>
                    </future>
                  </futures>
                  <objects>
                    <object multiplicity="*">
                      <location> 0 </location>
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

  syntax Val ::= object(Int)

/* 
  Redefinition of the semantics for new.
  - an instance of the class is created and
    an unique identifier is assigned to it
  - then the constructor is called as an ususal method
  - the result is the identifier of the new object
*/
  rule <k> new Class:Id(Vs:Vals)
           => (object(Id) ! Class(Vs)).get; ~> object(Id) ...</k>
       <nextObjectId> Id:Int => Id +Int 1 </nextObjectId>
       (. => <object>...
                <location> Id </location>
                <k>  create(Class) </k>
                <envStack> ListItem((Object, <env>.Map</env>)) </envStack>
             ...</object>)

/*
  The redefinition of the semantics for this:
*/

  rule <k> this => object(Id) ...</k>
       <location> Id:Int </location>

/*
  The semantics of the method call with futures.
*/

  // the arguments are strict such that they are evaluated first
  context object(_) ! Method:Id(HOLE)

  // future identifiers
  syntax Val ::= future(Int)

/*
  - a method call creates a new futures and "returns" the identifier
    of the new future 
*/
  rule <k> object(X:Int) ! Method:Id(Vs:Vals)
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
       <futureId> _ => F </futureId>
       <blocked-threads> . </blocked-threads>
       <threads>
         .
         =>
         <thread>...
           <k> lookupMember(<envStack> ES </envStack>, Method) ( Vs ) </k>
         ...</thread>
       </threads>
       <future> 
         <fid> F:Int </fid>
         <oid> Id:Int </oid>
         <method> Method:Id </method>
         <arguments> Vs:Vals </arguments>
         <state> sleeping => active </state>
       </future>
    [computational]

/*
  The semantics of a local call (???)
*/

  rule <k> methodClosure(_->T,Class,OL,Ps,S)(Vs:Vals) 
           => mkDecls(Ps,Vs) S
       </k>
       <crntClass> _ => Class </crntClass>
/*
  The semantics of a complete method call
*/

  rule object(Id:Int) . Method:Id(Vs:Vals) => (object(Id) ! Method(Vs)).get

/*
  The rules for blocking/unblocking tasks:
*/

  // the case when the future is not donne
  rule (<thread> <k> future(Id).get ~> K </k> T:Bag </thread> => . ) 
       (. => <blocked-thread> <guard> future(Id).get ~> K </guard> 
                              <blocked-thread-conf> T </blocked-thread-conf>
             </blocked-thread>)
       <fid> Id </fid>
       <state> S:State </state>
       requires S =/=K completed [computational]

  // the case when the future is done
  rule (. => <thread> <k> future(Id).get ~> K </k> T:Bag </thread>) 
       (<blocked-thread> <guard> future(Id).get ~> K </guard> 
                         <blocked-thread-conf> T </blocked-thread-conf>
        </blocked-thread> => .)
       <fid> Id </fid>
       <state> completed </state>

/*
  The rule that transform an active task into an waiting task
*/
/*
  rule <futureId> F </futureId>
       <blocked-threads> BT:Bag => . </blocked-threads>
       <threads> . </threads>
       (. => <waiting-task> <fId> F </fId>
                            <task-guards> getGuards(BT) </task-guards> 
                            <waiting-task-conf> BT </waiting-task-conf> 
             </waiting-task>)
       //<token> .K => 0 </token>
      requires notBool(BT ==Bag .Bag)
   [computational]
*/
 
/* 
  Since the above rule create nonterminating executions,
  it is replaced by the following one.
  The mai change is that a sleeping future automatically becomes
  the next active task.
*/
  rule <location> Id </location>
       <envStack> ES:List </envStack>
       <futureId> F => F' </futureId>
       <blocked-threads> BT:Bag => . </blocked-threads>
       <threads>
         .
         =>
         <thread>...
           <k> lookupMember(<envStack> ES </envStack>, Method) ( Vs ) </k>
         ...</thread>
       </threads>
       (. => <waiting-task> <fId> F </fId>
                            <task-guards> getGuards(BT) </task-guards> 
                            <waiting-task-conf> BT </waiting-task-conf> 
             </waiting-task>)
       <future> 
         <fid> F':Int </fid>
         <oid> Id:Int </oid>
         <method> Method:Id </method>
         <arguments> Vs:Vals </arguments>
         <state> sleeping => active </state>
       </future>
      requires notBool(BT ==Bag .Bag)
   [computational]

/*
  The rule transforming a waiting task into an active one. 
*/
  rule <blocked-threads> . => BT </blocked-threads>
       <threads> . </threads>
       <futureId> _ => F </futureId>
       (<waiting-task> <fId> F </fId> 
                       <task-guards>... SetItem(future(Id).get) ...</task-guards> 
                       <waiting-task-conf> BT </waiting-task-conf> 
        </waiting-task> => .)
       <fid> Id </fid>
       <state> completed </state>
    [computational]

/*
  The new semantics of the return statement:
*/

  rule
    <futureId> Id </futureId> 
//    (<threads>... <k> return V:Val; ...</k> ...</threads> => <threads> . </threads>)  // all threads removed???
    (<thread>... <k> return V:Val; ...</k> ...</thread> => .)
    <future>... <fid> Id </fid>
                <state> active => completed </state>
                (. => <result> V </result>)
    ...</future>

/*
  The sematics of the get metod:
*/

  rule <k> future(Id).get => V ...</k>
       <fid> Id </fid>
       <result> V </result>

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
