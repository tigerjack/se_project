module Cars
open util/boolean
open GeoUtilities
open Persons

/*
	SIGNATURES
*/
sig Car {
	batteryStatus: one BatteryStatus,
	availableSeats: some CarSeat,
	usedSeats: set Person,
	damages: set Damage,
	currentState: one CarState,
	pluggedStatus: one PluggedStatus,
	engineStatus: one EngineStatus,
	//N.B.: This means that every car in every moment occupies a range of points
	carPoints: some Point
}
{

	#usedSeats <= #availableSeats
//	usedSeats != none implies usedSeats & User != none
	usedSeats != none implies currentState = InUse
	currentState != none
	currentState != InUse implies usedSeats = none
	currentState = InUse implies pluggedStatus = PluggedOff
	(currentState in Reserved + Available) implies 
		batteryStatus = HighBattery
	currentState = InUse implies batteryStatus != ZeroBattery
	(batteryStatus = LowBattery and
		currentState != InUse and
		pluggedStatus = PluggedOff) implies 
		currentState = Unavailable
	engineStatus = EngineOn implies currentState = InUse
	currentState != InUse implies engineStatus = EngineOff
}

abstract sig BatteryStatus {}
// Battery less than or greater than 20%
sig LowBattery, HighBattery extends BatteryStatus {} 
sig ZeroBattery extends LowBattery{}

abstract sig EngineStatus {}
sig EngineOn, EngineOff extends EngineStatus {}

abstract sig PluggedStatus {}
sig PluggedOn, PluggedOff extends PluggedStatus {}

abstract sig CarState {}
sig Available, Unavailable, Reserved, InUse extends CarState {}

sig CarSeat {}

abstract sig Damage {}
sig MajorDamage, MinorDamage extends Damage {}

/*
	FACTS
*/
// Trivial relations
fact allEngineStatusAreAssociatedToSomeCar {
	all es: EngineStatus | es in Car.engineStatus
}

fact allPluggedStatusAreAssociatedToSomeCar {
	all ps: PluggedStatus |  ps in Car.pluggedStatus

}

fact allBatteryStatusMustBeAssociatedToSomeCar {
	all b: BatteryStatus | b in Car.batteryStatus
}

fact allCarStatesMustBeAssociatedToSomeCars {
	all cs: CarState | cs in Car.currentState
}

fact allCarSeatsMustBeAssociatedToOneCar {
	all cs: CarSeat | one c: Car | cs in c.availableSeats
}

fact damagesMustBeAssociatedToACar {
	all d: Damage | d in Car.damages
}


// Others
fact carsPositionsDoNotOverlap {
	all disj c1, c2: Car | c1.carPoints & c2.carPoints = none
}

fact personsAreNotUbiquituous {
	all disj c1, c2: Car | no p: Person | p in c1.usedSeats and p in c2.usedSeats
}

fact personsInUsedSeatsHaveSamePositionOfCar {
	all c: Car, p: Person | p in c.usedSeats iff p.personPoint in c.carPoints 
}

fact majorDamagesImpliesUnavailableCars {
	all c: Car, m: MajorDamage | m in c.damages implies 
		c.currentState = Unavailable
}


/**
	ASSERTS
*/
assert allCarsHaveDifferentPositions {
	all disj c1, c2: Car | no c1.carPoints & c2.carPoints
}
check allCarsHaveDifferentPositions for 10

assert allPersonsCantBeInDifferentCars {
	all disj c1, c2: Car | no p: Person |
		p in c1.usedSeats and p in c2.usedSeats
}
check allPersonsCantBeInDifferentCars for 10

assert allPersonsInACarMustHaveThatCarPosition {
	all p: Person, c: Car | p in c.usedSeats implies 
		p.personPoint in c.carPoints
}

assert allMajorDamagedCarsAreUnavailable {
	all m: MajorDamage, c: Car | m in c.damages implies
		c.currentState = Unavailable
}
check allMajorDamagedCarsAreUnavailable for 10

assert allReservedOrAvailableCarsHaveHighBatteries {
	all c: Car | c.currentState in (Reserved + Available) implies 
		c.batteryStatus = HighBattery
}
check allReservedOrAvailableCarsHaveHighBatteries for 3

assert noCarInUseHaveZeroBattery {
	no c: Car | c.currentState = InUse and c.batteryStatus = ZeroBattery
}
check noCarInUseHaveZeroBattery for 10

assert allCarWithUsedSeatsShouldBeInUse {
	all c: Car | c.usedSeats != none implies c.currentState = InUse
}
check allCarWithUsedSeatsShouldBeInUse for 10

assert allCarsNotInUseAndNotPluggedAndWithLowBatteryShouldBeUnavailable {
	all c: Car | (c.batteryStatus = LowBattery and
		c.currentState != InUse and
		c.pluggedStatus = PluggedOff) implies 
		c.currentState = Unavailable
}
check allCarsNotInUseAndNotPluggedAndWithLowBatteryShouldBeUnavailable for 10

assert noPluggedCarIsInUse {
	all c: Car | c.currentState = InUse implies c.pluggedStatus = PluggedOff
}
check noPluggedCarIsInUse for 10

assert allEnginesOnAreAssociatedToInUseCars {
	all c: Car | c.engineStatus = EngineOn implies c.currentState = InUse
}
check allEnginesOnAreAssociatedToInUseCars for 3

assert allUsedSeatsHaveSamePositionOfCars {
	all c: Car | c.usedSeats != none implies 
		c.usedSeats.personPoint in c.carPoints
}
check allUsedSeatsHaveSamePositionOfCars for 3


/*
	PREDICATES/FUNCTIONS
*/
pred show() {
	#Car > 0
//	#Person > 1
//	#(Car.currentState & Reserved) = #Car
//	Car.currentState & Available = none
/*
	#InUse > 0
	#Unavailable > 0
	#Reserved > 0
	#Available > 0

	#MajorDamage > 0
	#MinorDamage > 0
	#Damage > 0
*/
}
run show for 3

pred showCouldExistSomeUnavailableCarWithNoMajorDamageAndHighBattery {
	#Car > 0
	#Unavailable = #Car
	#MajorDamage = 0
	#LowBattery = 0
	#Person = 0
}
run showCouldExistSomeUnavailableCarWithNoMajorDamageAndHighBattery for 3

pred showCouldExistSomeAvailableCarWithMinorDamages {
	#MinorDamage = #Car
	#Available = #Car
}
run showCouldExistSomeAvailableCarWithMinorDamages for 3

pred showCouldExistSomeInUseCarsWithEngineOff {
	#Car > 0
	#InUse = #Car
	#EngineOff = #Car
}
run showCouldExistSomeInUseCarsWithEngineOff for 3

pred showCouldExistSomeInUseCarsWithEngineOnAndPersonsOutside {
	#Car > 0
	#InUse = #Car
	#EngineOn = #Car
	#Point = #Person
	#Person > #Car
}
run showCouldExistSomeInUseCarsWithEngineOnAndPersonsOutside for 3

pred showCouldExistSomeInUseCarsWithSeatsOccupiedByNonUsers {
	#Car > 0
	#Person > 0
}
run showCouldExistSomeInUseCarsWithSeatsOccupiedByNonUsers for 3


pred showMorePersonsInOneCar {
	#Car.usedSeats > 1
	#Car = 1
}
run showMorePersonsInOneCar for 5
