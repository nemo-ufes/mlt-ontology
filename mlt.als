module multilevelmodelling

sig Entity{
  iof: set Entity,
  specializes: set Entity,
  properSpecializes: set Entity,
  powertypeOf: set Entity,
  characterizes: set Entity,
  compCharacterizes: set Entity,
  disjCharacterizes: set Entity,
  partitions: set Entity,
  isSubordinateTo: set Entity
}

one sig Individual extends Entity{}

one sig FOT extends Entity{}

one sig SOT extends Entity{}

one sig TOT extends Entity{}

fact instancesOfIndividualHaveNoInstances{
	all x:Entity, ind:Individual | ( ind in x.iof implies no iof.x)
 	all x:Entity| no iof.x implies one ind:Individual |  ind in x.iof
}

fact instancesOfFOTHaveIndividualsAsInstances{
	all x:Entity, f:FOT, i:Individual|  f in x.iof iff i in x.specializes
}

fact instancesOfSOTHaveInstancesOfFOTAsInstances{
	all x:Entity, f:FOT, s:SOT|  s in x.iof iff f in x.specializes
}

fact instancesOfTOTHaveInstancesOfSOTAsInstances{
	all x:Entity, t:TOT, s:SOT|  t in x.iof iff s in x.specializes
}

fact individualFOTSOTAndTOTAreComplete{
	all s:SOT, f:FOT, i:Individual, t:TOT, x:Entity| f in x.iof or i in x.iof or  s in x.iof or  t in x.iof or x=t
}

fact individualFOTSOTAndTOTAreDisjoint{
	all s:SOT, f:FOT, i:Individual, t:TOT| no x:Entity| (f in x.iof and i in x.iof) or (s in x.iof and i in x.iof) or (t in x.iof and i in x.iof) or (f in x.iof and s in x.iof) or (f in x.iof and t in x.iof) or (t in x.iof and s in x.iof)
}

fact equalityOfTypesDef{
	all x,y:Entity, i:Individual|  i not in y.iof and i not in x.iof implies (iof.x = iof.y iff x=y)
}

fact specializationDef{
	all x,y:Entity | x in y.specializes iff all z:Entity, i:Individual | i not in y.iof and i not in x.iof and (y in z.iof implies x in z.iof)
}

fact properSpecializationDef{
	all x,y:Entity | (x in y.specializes and x!=y) iff x in y.properSpecializes
}

fact powertypeDef{
	all x,y:Entity | y in x.powertypeOf iff (all z:Entity, i:Individual | i not in y.iof and i not in x.iof and (x in z.iof iff y in z.specializes))
}

fact characterizationDef{
	all x,y:Entity | y in x.characterizes iff (all w:Entity , i:Individual | i not in y.iof and i not in x.iof and (x in w.iof implies y in w.properSpecializes))
}

fact compCharacterizationDef{
	all x,y:Entity | y in x.compCharacterizes iff (y in x.characterizes and (all z:Entity | y in z.iof implies (some w:Entity | w in z.iof and x in w.iof)))
}

fact disjCharacterizationDef{
	all x,y:Entity | y in x.disjCharacterizes iff (y in x.characterizes and (all z:Entity | y in z.iof implies (lone w:Entity | w in z.iof and x in w.iof)))
}

fact partitionsDef{
	all x,y:Entity | y in x.partitions iff (y in x.disjCharacterizes and y in x.compCharacterizes)
}

fact subordinationDef{
	all x,y:Entity | y in x.isSubordinateTo iff (all w:Entity, i:Individual|i not in x.iof and (x in w.iof implies (some z:Entity| y in z.iof  and z in w.properSpecializes)))
}

//--------Assertions

pred basicIofRelations{
	//Individual iof FOT
	all i:Individual, f:FOT | f in i.iof
	//FOT iof SOT
	all f:FOT, s:SOT | s in f.iof
	//SOT iof TOT
	all t:TOT, s:SOT | t in s.iof
}

pred basicPowertypeRelations{
	all i:Individual, f:FOT | i in f.powertypeOf
	all f:FOT, s:SOT | f in s.powertypeOf
	all s:SOT, t:TOT | s in t.powertypeOf
}

pred iofProperties{
	//Assymetric
	all x,y:Entity | x in y.iof => y not in x.iof
	//Irreflexive
	all x:Entity | x not in x.iof
	//Intransitive
	all x,y,z:Entity | (y in x.iof and z in y.iof) => z not in x.iof
	//Acyclic
	all x:Entity | x not in x.^iof
}

pred specializationProperties{
	//Antissymetric
	all x,y:Entity | (x in y.specializes and x!=y) => y not in x.specializes
	//Reflexive
	all x:Entity, i:Individual | i not in x.iof => x  in x.specializes
	//Transitive
	all x,y,z:Entity | (y in x.specializes and z in y.specializes) => z  in x.specializes
}

pred atMostOnePowertype{
//Each entity has at most one powertype
	all x:Entity| lone powertypeOf.x
}

pred specializationAndPowertypeTransitivity{
//If a type x specializes another type y then the powertype of x specializes the powertype of y
	all x,y,w,z:Entity | (y in x.specializes and x in w.powertypeOf and y in z.powertypeOf) implies z in w.specializes
}

pred RelationsBetweenBasicTypes{
//Every instance of FOT specializes Individual and
//Every specialization of Individual is iof FOT
all x:Entity, f:FOT, i:Individual | f in x.iof iff i in x.specializes
//Every instance of SOT specializes FOT and
//Every specialization of FOT is iof SOT
all x:Entity, f:FOT, s:SOT | s in x.iof iff f in x.specializes
//Every instance of TOT specializes SOT and
//Every specialization of SOT is iof TOT
all x:Entity, t:TOT, s:SOT | t in x.iof iff s in x.specializes
}

//if a type x characterizes a type y then x characterizes all supertypes of y
pred characterizationTransitivityThroughSpecialization{
	all x,y:Entity| y in x.characterizes implies all z:Entity | (z in y.specializes implies z in x.characterizes)
}

//Is it possible to have a supertype of Individual, or FOT or SOT, or TOT??
pred supertypesOfFoundationTypes{
	all i:Individual, s:SOT, f:FOT, t:TOT | some i.specializes or some f.specializes or some s.specializes or some t.specializes
}


//∀t1,t2,t3 (isPowertypeOf(t2,t1)∧characterizes(t3,t1))→properSpecializes(t3,t2)
pred theoremT12{
	all t1,t2,t3:Entity | (t1 in t2.powertypeOf and t1 in t3.characterizes) implies t2 in t3.properSpecializes
}

//∀ t1,t2,t3,t4 (specializes(t2,t1)∧isPowertypeOf(t4,t2)∧isPowertypeOf(t3,t1))→specializes(t4,t3)
pred theoremT13{
	all t1,t2,t3,t4:Entity | (t1 in t2.specializes and t2 in t4.powertypeOf and t1 in t3.powertypeOf) implies t3 in t4.specializes
}


//∀ t1,t2,t3,t4 (partitions(t1,t3)∧partitions(t2,t3))→¬properSpecializes(t1,t2)
pred theoremT14{
	all t1,t2,t3:Entity | (t3 in t1.partitions and t3 in t2.partitions) implies (t2 not in t1.properSpecializes)
}

--------

assert allassertions
{ 
basicPowertypeRelations
and iofProperties
and specializationProperties
and  atMostOnePowertype
and  specializationAndPowertypeTransitivity
and  RelationsBetweenBasicTypes
and  characterizationTransitivityThroughSpecialization
and  supertypesOfFoundationTypes
and  theoremT12
and  theoremT13
and  theoremT14 
}

check allassertions for 10






