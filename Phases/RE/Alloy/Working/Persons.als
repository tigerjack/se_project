module Persons
open GeoUtilities

/**
	SIGNATURES
*/
sig Person {
	// We assume that each Person is identified by only one point
	personGpsVolume: one GpsVolume
}
sig User extends Person {}

/**
	PREDICATES/FUNCTIONS
*/
pred show() {
	#Person > 3
}
run show for 6

pred showCouldExistOverlappingPersons() {
	#Person > 1
	#User = 0
	some disj p1, p2: Person | 
		p1.personGpsVolume = p2.personGpsVolume
	GpsVolume in Person.personGpsVolume
}
run showCouldExistOverlappingPersons for 2

pred showCouldExistNearbyPersons() {
	#Person > 1	
	some disj p1, p2: Person | 
		p1.personGpsVolume.gpsPoints & p2.personGpsVolume.gpsPoints != none
}
run showCouldExistNearbyPersons for 4
