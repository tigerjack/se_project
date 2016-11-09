module Cars
open util/boolean

/*
	SIGNATURES
*/
sig Car {
	battery: one Battery,
	seats: Int,
	usedSeats: Int,
	damages: set Damage,
	currentState: one CarState,
	plugged: one Bool
//	code: one CarCode,
//	plug: one Plug,
//	currentPosition: one GPSPoint
}
{
	seats > 0 and seats <= 4 
	usedSeats >= 0 and usedSeats <= seats
	currentState != none
//	Not necessary true, a user can f.e. exit from a car while still using it
//	currentState = InUse implies usedSeats > 0
	currentState != InUse implies usedSeats = 0
	currentState = Reserved implies battery.statusPercentage >= 20
	currentState = InUse implies battery.statusPercentage > 0
	(battery.statusPercentage < 20 and
		currentState != InUse and
		plugged = False) implies 
		currentState = Unavailable
}

sig Battery {
	statusPercentage: Int
}
{
	statusPercentage >= 0 statusPercentage <= 100
}

// Check difference b/w enum and abstract

abstract sig Damage {}
sig MajorDamage, MinorDamage extends Damage {}

abstract sig CarState {}
sig Available, Unavailable, Reserved, InUse extends CarState {}

/*
enum Damage {
	MajorDamage, MinorDamage
}

enum CarState {
	Available, Unavailable, Reserved, InUse, Plugged
}
*/


/*
	FACTS
*/
fact batteriesMustBeAssociatedToOneVehicle {
	all b: Battery | one c: Car | b in c.battery
}

fact damagesMustBeAssociatedToACar {
	all d: Damage | d in Car.damages
}

fact carStatesMustBeAssociatedToSomeCars {
//	It reaches the same end goal, but generates an additional relation
//	between a state and a car
//	all cs: CarState | some c: Car | cs in c.currentState
	all cs: CarState | cs in Car.currentState
}

fact majorDamagesImpliesUnavailableCars {
	all c: Car, m: MajorDamage | m in c.damages implies 
		c.currentState = Unavailable
}

/*
	ASSERTS
*/
assert allMajorDamagedCarsAreUnavailable {
	all m: MajorDamage, c: Car | m in c.damages implies
		c.currentState = Unavailable
}

assert allReservedCarsHasEnoughBattery {
	all c: Car | c.currentState = Reserved and 
		c.battery.statusPercentage >= 20
}

assert noCarInUseHaveZeroBattery {
	no c: Car | c.currentState = InUse and c.battery.statusPercentage = 0
}

assert allCarsNotInUseAndNotPluggedAndWithLowBatteryShouldBeUnavailable {
	all c: Car | (c.battery.statusPercentage < 20 and
		c.currentState != InUse and
		c.plugged = False) implies 
		c.currentState = Unavailable
}


/*
// Not true, a car may be minor damaged but still available (the 
// employee has manually set the status to available again)
assert allCarsUnusedAndMinorDamagedAreUnavailable {
	all c: Car, m: MinorDamage | m in c.damages implies 
		c.currentState = Unavailable 
}
*/


check allMajorDamagedCarsAreUnavailable for 8
check allReservedCarsHasEnoughBattery for 8
check allCarsNotInUseAndNotPluggedAndWithLowBatteryShouldBeUnavailable for 8
check noCarInUseHaveZeroBattery for 8

/*
	PREDICATES/FUNCTIONS
*/
pred show() {
	#Car > 0
	#(Car.currentState & Reserved) = #Car
//	Car.currentState & Available = none
/*
	#InUse > 0
	#Unavailable > 0
	#Reserved > 0
	#Plugged > 0
	#Available > 0
	#MajorDamage > 0
	#MinorDamage > 0
	#Damage > 0
	1 in Car.usedSeats
	0 in Battery.statusPercentage
	19 in Battery.statusPercentage
	20 in Battery.statusPercentage
*/
}

run show for 3 but 8 Int

/*
open Codes
open GPSUtilities

sig Plug {}
sig CarCode extends Code {}

fact carCodesAreAssociatedToOneCar {
	all cc: CarCode | one c: Car | cc in c.code
}
fact plugsMustBeAssociatedToOneVehicle {
	 all p: Plug | one c: Car | p in c.plug 
}

fact codesAreUniques {
	all c1, c2: Car | (c1 != c2) implies (c1.code != c2.code)
}
*/
