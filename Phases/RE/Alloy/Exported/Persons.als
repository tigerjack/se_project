module Persons
open GeoUtilities

/**
	SIGNATURES
*/
sig Person {
	// We assume that each Person is identified by only one point
	personPoint: one Point
}
sig User extends Person {}

/**
	FACTS
*/
fact personPositionsDoNotOverlap {
	all disj p1, p2: Person | p1.personPoint != p2.personPoint
}


/**
	ASSERTS
*/
assert allUsersHaveDifferentPositions {
	no disj p1, p2: Person | p1.personPoint = p2.personPoint
}
check allUsersHaveDifferentPositions for 10

/**
	PREDICATES/FUNCTIONS
*/
pred show() {
	#Person > 0
	#Point = #Person
}

run show for 25
