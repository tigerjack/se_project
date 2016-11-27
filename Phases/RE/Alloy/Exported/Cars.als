module Cars
//open util/boolean
open GeoUtilities
open Persons

/*
	SIGNATURES
*/
sig Car {
	batteryStatus: one BatteryStatus,
	carSeats: some CarSeat,
	usedSeats: Person lone -> lone carSeats,
	damages: set Damage,
	currentState: one CarState,
	pluggedStatus: one PluggedStatus,
	engineStatus: one EngineStatus,
	carGpsVolume: one GpsVolume
}
{
	(usedSeats.carSeats) != none implies currentState = InUse
	currentState != none
	currentState != InUse implies (usedSeats.carSeats) = none
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
lone sig LowBattery, HighBattery extends BatteryStatus {} 
lone sig ZeroBattery extends LowBattery{}

abstract sig EngineStatus {}
lone sig EngineOn, EngineOff extends EngineStatus {}

abstract sig PluggedStatus {}
lone sig PluggedOn, PluggedOff extends PluggedStatus {}

abstract sig CarState {}
lone sig Available, Unavailable, Reserved, InUse extends CarState {}

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
	all cs: CarSeat | one c: Car | cs in c.carSeats
}

fact damagesMustBeAssociatedToACar {
	all d: Damage | d in Car.damages
}


// Others
fact personsAreNotUbiquituous {
	all disj c1, c2: Car | no p: Person | 
		p in (c1.usedSeats).CarSeat and 
		p in (c2.usedSeats).CarSeat
}

fact personsInUsedSeatsHaveSamePositionOfCar {
	all c: Car, p: Person | p in (c.usedSeats).CarSeat implies 
		p.personGpsVolume.gpsPoints & c.carGpsVolume.gpsPoints != none 
}

fact majorDamagesImpliesUnavailableCars {
	all c: Car, m: MajorDamage | m in c.damages implies 
		c.currentState = Unavailable
}


/**
	ASSERTS
*/
assert allPersonsCantBeInDifferentCars {
	all disj c1, c2: Car | no p: Person |
		p in (c1.usedSeats).CarSeat and p in (c2.usedSeats).CarSeat
}
check allPersonsCantBeInDifferentCars for 10

assert allPersonsInACarMustHaveThatCarPosition {
	all p: Person, c: Car | p in (c.usedSeats).CarSeat implies 
		p.personGpsVolume.gpsPoints & c.carGpsVolume.gpsPoints != none
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
	all c: Car | (c.usedSeats).CarSeat != none implies c.currentState = InUse
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
	all c: Car | (c.usedSeats).CarSeat != none implies 
		(c.usedSeats).(c.carSeats).personGpsVolume.gpsPoints & 
		 c.carGpsVolume.gpsPoints != none
}
check allUsedSeatsHaveSamePositionOfCars for 3


/*
	PREDICATES/FUNCTIONS
*/
// A car may be perfectly functioning but still unavailable (the external  
// employee has manually set the status to Unavailable) 
pred showCouldExistSomeUnavailableCarWithNoMajorDamageAndHighBattery {
	#Car > 0
	#Unavailable = #Car
	#MajorDamage = 0
	#LowBattery = 0
	#Person = 0
	GpsVolume in (Car.carGpsVolume + Person.personGpsVolume)

}
run showCouldExistSomeUnavailableCarWithNoMajorDamageAndHighBattery for 3

pred showCouldExistSomeCarWithLoweBattery {
	#Car > 0
	#LowBattery > 0
}
run showCouldExistSomeCarWithLoweBattery for 3

// A car may have minor damages but still available (the external  
// employee has manually set the status to Available)
pred showCouldExistSomeAvailableCarWithMinorDamages {
	#MinorDamage = #Car
	#Available = #Car
}
run showCouldExistSomeAvailableCarWithMinorDamages for 3

// It does mean that a User has turned the engine off outside a parking area
pred showCouldExistSomeInUseCarsWithEngineOff {
	#Car > 0
	#InUse = #Car
	#EngineOff = #Car
}
run showCouldExistSomeInUseCarsWithEngineOff for 3

// Same as before, all the people have left the car, even it is still in use
pred showCouldExistSomeInUseCarsWithEngineOnAndAllPersonsOutside {
	#Car > 0
	#InUse = #Car
	#EngineOn = #Car
	#Person > 0
	#Damage = 0
	#CarSeat = #Car
	#Car.usedSeats = 0
	GpsVolume in (Car.carGpsVolume + Person.personGpsVolume)
}
run showCouldExistSomeInUseCarsWithEngineOnAndAllPersonsOutside for 6

// Not only users have access to the car. We ensure that a User reserve a Car, 
// but we don't know if he/she will use it.
pred showCouldExistSomeInUseCarsWithAllSeatsOccupiedByNonUsers {
	#Car > 0
	#Person > 0
	#User = 0
}
run showCouldExistSomeInUseCarsWithAllSeatsOccupiedByNonUsers for 3

// Show that different people can be in the same car
pred showMorePersonsInOneCar {
	#Car.usedSeats > 1
	#Car = 1
}
run showMorePersonsInOneCar for 7

pred show() {
	#Car > 0
	#Person > 0
	#GpsVolume > 1
	#Car.damages < 3
}
run show for 3
