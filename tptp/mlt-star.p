%
%  A fragment of MLT-star formalization
% (partly based on https://doi.org/10.1007/978-3-319-69904-2_2 )
%
% João Paulo A. Almeida, 13-May-2020
%
% All conjectures proven with http://www.tptp.org/cgi-bin/SystemOnTPTP
% (Only one conjecture at a time admitted by the system, comment all conjectures
% not being investigated.)
%

%%%%% Top fragment of MLT-star

% All elements in the domain of quantification are entities
fof(a1, axiom, (
	![X] : (entity(X))
	)).

% Individual definition
fof(a2, axiom, (
	![X] : (individual(X) <=> ~?[Y] : iof(Y,X))
	)).

% Type definition
fof(a3, axiom, (
	![X] : (type_(X) <=> ?[Y] : iof(Y,X))
	)).

% Sanity check: Types and individuals partition entity
fof(typesAndIndividualsPartitionEntity, conjecture, (
	![X]: (type_(X)|individual(X)) &
	~?[X]: (type_(X)&individual(X))	
)).

% Auxiliary definitions to write a4 (without transitive iof')
% We need the notion of 'set of types' 
% We do not necessitate infinite sets, but all possible sets considering the existing types
% We do not necessitate the empty set

% A singleton set exists for every type
fof(singleton, axiom, (
	![X] : (type_(X) => (?[Y]: (set_(Y) & member(X,Y) & ![Z]:(member(Z,Y)=>(Z=X)))))
)).

% Unions exists for every pair of sets
fof(unions, axiom, (
	![X,Y] : ((set_(X)&set_(Y)) => 
		?[Z]: (set_(Z)& ![E]: (member(E,Z) <=> (member(E,X)|member(E,Y)))) )
)).

% Set identity (extensionality)
fof(setidentity, axiom, (
	![S1,S2] :
	( (set_(S1) & set_(S2)) => ((S1=S2) <=> ![X]:(member(X,S1)<=>member(X,S2))))
	)).

% We are only concerned with sets of types, membership is only meaningful for sets and types
fof(membershiptyping, axiom, (
	![X,Y] : (member(X,Y) => (set_(Y)&type_(X)))
)).

% Sets are individuals
fof(setsareindividuals, axiom, (
	![X] : (set_(X) => individual(X))
)).

% end of auxiliary definitions to write a4

% Types are ultimately grounded on individuals
%
% For all non-empty set of types
% there exists a member of the set that has an instance that is not the a member of the set
fof(a4, axiom, (
	![X]: ( (set_(X) & (?[Y]:(member(Y,X))) & (![Y]: (member(Y,X)=>type_(Y))) ) =>
		?[Y]: (member(Y,X) & ?[Z]: (iof(Z,Y)&~member(Z,X)))
	)
)).

% Definition for first-order type
fof(a5_firstOrderTypeDef, axiom, (
	![X]: (firstordertype(X) <=>
		(
			type_(X)&
			![Y]: (iof(Y,X)=>individual(Y))
		)
	)
)).

% Definition for second-order type
fof(a6_secondOrderTypeDef, axiom, (
	![X]: (secondordertype(X) <=>
		(
			type_(X)&
			![Y]: (iof(Y,X)=>firstordertype(Y))
		)
	)
)).

% Specialization definition
fof(a7_specDef, axiom, (
	![T1,T2] :
	(specializes(T1,T2) <=> (type_(T1) & ![E]:(iof(E,T1) => iof(E,T2)))) 
	)).
	
% Proper specialization definition
fof(a8_properSpecDef, axiom, (
	![T1,T2] :
	(properSpecializes(T1,T2) <=> (specializes(T1,T2) & ~(T1=T2))) 
	)).

% Type equality
fof(a9_equality, axiom, (
	![T1,T2] :
	( (type_(T1) & type_(T2)) => ((T1=T2) <=> ![X]:(iof(X,T1)<=>iof(X,T2)))) 
	)).

% Cardelli powertype definition
fof(a10_isPowertypeOfDef, axiom, (
	![T1,T2] :
	(isPowertypeOf(T1,T2) <=> (type_(T1) & ![T3]:(iof(T3,T1)<=>specializes(T3,T2)))) 
	)).

% Odell powertype definition
fof(a11_categorizationDef, axiom, (
	![T1,T2] :
	(categorizes(T1,T2) <=> (type_(T1) & ![T3]:(iof(T3,T1)=>properSpecializes(T3,T2)))) 
	)).

% Subordination definition
fof(a12_subordinationDef, axiom, (
	![T1,T2] :
	(isSubordinateTo(T1,T2) <=> (
			type_(T1) & type_(T2) & 
			![T3,T4]:( (iof(T3,T1)&iof(T4,T2))=>properSpecializes(T3,T4)))
	) 
	)).

% Complete categorization definition
fof(completeCategorizationDefinition, axiom, (
	![T1,T2] :
	(completelyCategorizes(T1,T2) <=> (categorizes(T1,T2) &
		![E]:(iof(E,T2)=>?[T3]:(iof(E,T3)&iof(T3,T1)))))
	)).

% Disjoint categorization definition
fof(disjointCategorizationDefinition, axiom, (
	![T1,T2] :
	(disjointlyCategorizes(T1,T2) <=> (categorizes(T1,T2) &
		![E,T3,T4]:((iof(T3,T1)&iof(T4,T1)&iof(E,T3)&iof(E,T4))=>T3=T4)))
	)).

% Partitioning definition
fof(partitioningDefinition, axiom, (
	![T1,T2] :
	(partitions(T1,T2) <=> (completelyCategorizes(T1,T2)&disjointlyCategorizes(T1,T2)))
	)).

%
% Constants definition
%
fof(a13_individualConstantDef, axiom, ( 
	![T] : ((T=c_individual) <=> ![X]:( iof(X,T)<=>individual(X)))
)).

fof(a14_fotConstantDef,axiom,(
	![T] : ((T=c_fot) <=> ![X]:(iof(X,T)<=>firstordertype(X)))
)).

fof(a15_sotConstantDef,axiom,(
	![T] : ((T=c_sot) <=> ![X]:(iof(X,T)<=>secondordertype(X)))
)).


%%%%% Theorems on powertypes


% The basetype T is unique given a (Cardelli) powertype P
fof(t1_basetypeUnique, conjecture, (
	![P,T] :
	(isPowertypeOf(P,T) => ~?[P_]:((~(P_=P))&(isPowertypeOf(P_,T))))  
)).

% The powertype P is unique given a basetype T
fof(t2_powertypeUnique, conjecture, (
	![P,T] :
	(isPowertypeOf(P,T) => ~?[T_]:((~(T_=T))&(isPowertypeOf(P,T_))))  
)).

% If a type t1 specializes a type t2 then the (Cardelli) powertype of t1
% specializes the (Cardelli) powertype of t2. 
fof(t3, conjecture, (
	![T1,T2,T3,T4] :
	((specializes(T1,T2)&isPowertypeOf(T3,T1)&isPowertypeOf(T4,T2))=>specializes(T3,T4))  
)).

% Odell powertypes (categorizations in MLT*) proper specialize the Cardelli 
% powertype of a base type
fof(t4, conjecture, (
	![T1,T2,T3] :
	((isPowertypeOf(T2,T1)&categorizes(T3,T1))=>(properSpecializes(T3,T2)))
)).

% If two types both partition the same type, then they cannot proper specialize each other
fof(t5, conjecture, (
	![T1,T2,T3] :
	((partitions(T1,T3)&partitions(T2,T3))=>(~properSpecializes(T1,T2)))
)).


% A first-order type is never a powertype
fof(powertypeNotFirstOrder, conjecture, (
		![X,Y]: ( isPowertypeOf(X,Y) => ~firstordertype(X))
)).


%%%%% Theorems corresponding to the anti-patterns

% AP1
fof(ap1,conjecture,(
	~?[T1,T2] : (individual(T1)&iof(T2,T1))
)).

% AP2
fof(ap2,conjecture,(
	~?[T1,T2] : (iof(T1,c_sot)&iof(T2,c_sot)&iof(T2,T1))
)).

% AP3
fof(ap3,conjecture,(
	~?[T] : (iof(T,c_sot)&specializes(T,c_sot))
)).




