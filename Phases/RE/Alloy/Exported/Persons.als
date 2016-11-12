module Persons
open GeoUtilities

/**
	SIGNATURES
*/
abstract sig Person {
	currentPosition: one Position
}
sig User, Passenger extends Person {}

/**
	FACTS
*/
fact usersPositionsDoNotOverlap {
	all disj u1, u2: User | u1.currentPosition != u2.currentPosition
}

/**
	ASSERTS
*/
assert allUsersHaveDifferentPositions {
	no disj u1, u2: User | u1.currentPosition = u2.currentPosition
}
check allUsersHaveDifferentPositions for 10

/**
	PREDICATES/FUNCTIONS
*/
pred show() {
	#User > 0
}

run show for 25
