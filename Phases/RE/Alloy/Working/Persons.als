module Persons
open GeoUtilities

/**
	SIGNATURES
*/
sig Person {
	personPosition: one Position
}
sig User extends Person {}

/**
	FACTS
*/
fact personPositionsDoNotOverlap {
	all disj p1, p2: Person | p1.personPosition != p2.personPosition
}

/**
	ASSERTS
*/
assert allUsersHaveDifferentPositions {
	no disj u1, u2: User | u1.personPosition = u2.personPosition
}
check allUsersHaveDifferentPositions for 10

/**
	PREDICATES/FUNCTIONS
*/
pred show() {
	#User > 0
}

run show for 25
