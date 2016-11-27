module Areas
open Cars
open GeoUtilities

/**
	SIGNATURES
*/
abstract sig CompanyCarSlot {}
sig ParkingSlot, ChargingSlot extends CompanyCarSlot {}

abstract sig CompanyArea {
	// We assume that a CompanyArea is composed by a non empty set of Points
	// This is enough for our modelation of the world
	areaGpsPoints: some GpsPoint
}

sig ParkingArea extends CompanyArea {
	parkingSlots: set ParkingSlot,
	parkedCars: Car lone -> lone parkingSlots
}

sig ChargingArea extends ParkingArea {
	chargingSlots: some ChargingSlot,
	chargingCars: Car lone -> lone chargingSlots
}

/**
	FACTS
*/
// Trivial
/*
fact parkingSlotsAreaAssociatedToExactlyOneArea {
	all pa1: ParkingArea, pa2: ParkingArea | 
		(pa1.parkingSlots & pa2.parkingSlots) != none iff
		pa1 = pa2
}
*/
fact parkingSlotsAreaAssociatedToExactlyOneArea {
	all ps: ParkingSlot | one pa: ParkingArea | ps in pa.parkingSlots
}

fact chargingSlotsAreaAssociatedToExactlyOneArea {
	all cs: ChargingSlot | one ca: ChargingArea | cs in ca.chargingSlots
}

// Areas do not overlap
fact areaPositionsAreAssociatedToExaxtlyOneCompanyArea {
//	Gps volumes for company area are predefined, so there is no way different 
//	areas overlap
	all disj a1, a2: CompanyArea | 
		a1.areaGpsPoints & a2.areaGpsPoints = none
}

// Parked Cars are in Parking Areas position
fact allParkedCarsAreInsideThoseAreaPositions {
	all pa: ParkingArea, c: Car | 
		c in (pa.parkedCars).(pa.parkingSlots) implies 
		c.carGpsVolume.gpsPoints & pa.areaGpsPoints != none
}

//Charging Cars are in Charging Areas position
fact allChargingCarsAreInsideThoseAreaPositions {
	all ca: ChargingArea, c: Car | 
		c in (ca.chargingCars).(ca.chargingSlots) implies 
		c.carGpsVolume.gpsPoints & ca.areaGpsPoints != none
}

// If a Car is inside an Area but not occupying a slot, it should be in use
fact allCarsInsideAreasButNotParkedOrChargingAreInUse {
	all c: Car |
		(c.carGpsVolume.gpsPoints in ParkingArea.areaGpsPoints and 
		 c not in 
		 ( (ParkingArea.parkedCars).ParkingSlot + 
		   (ChargingArea.chargingCars).ChargingSlot )) implies
		   c.currentState = InUse
}

// I.e. a ParkingArea has always a parkingCapacity > 0
fact parkingCapacityZeroCanOnlyBeAssociatedToChargingArea {
	all p: ParkingArea | p.parkingSlots = none implies 
		p in ChargingArea
}

// N.B. Implies and not Iff bcz a car in a ParkingArea can also be Unavailable
fact carStateAvailableOrReservedImpliesCarAtOneParkingArea {
	all c: Car, pa: ParkingArea, ca: ChargingArea | 
		(c.currentState = Available or c.currentState = Reserved) implies
		( (c in (pa.parkedCars).ParkingSlot) or
		  (c in (ca.parkedCars).ParkingSlot) or  
		  (c in (ca.chargingCars).ChargingSlot ))
}
// If a car is plugged <=> it must be in one charging area
fact carStatePluggedIffCarInOneChargingCars {
	all c: Car | one ca: ChargingArea | 
		c.pluggedStatus = PluggedOn iff c in (ca.chargingCars).(ca.chargingSlots)
}

fact carCantBeChargingAndParkedAtSameTime {
	no (ParkingArea.parkedCars).ParkingSlot & 
	    (ChargingArea.chargingCars).ChargingSlot
}

fact carParkedInOneParkingArea {
	all pa1, pa2: ParkingArea | 
		(pa1 != pa2 implies 
			(pa1.parkedCars).ParkingSlot & (pa2.parkedCars).ParkingSlot = none)
}

fact carChargingInOneChargingArea {
	all ca1, ca2: ChargingArea | 
		(ca1 != ca2 implies 
			(ca1.chargingCars).ChargingSlot & (ca2.chargingCars).ChargingSlot = none)
}

fact carStateInUseIfItIsNotInAParkingOrChargingSlot {
	all c: Car | c.currentState = InUse implies
		c not in ( (ParkingArea.parkedCars).ParkingSlot + 
			      (ChargingArea.chargingCars).ChargingSlot)
}

/**
	ASSERTS
*/
assert areaPositionsAreNotOverlapping {
	all disj ca1, ca2: CompanyArea | ca1.areaGpsPoints & ca2.areaGpsPoints = none
}
check areaPositionsAreNotOverlapping for 10

assert sameCarShouldNotBePluggedAtDifferentChargingArea {
	all c: Car | one ca: ChargingArea | 
		c.pluggedStatus = PluggedOn iff
		c in (ca.chargingCars).(ca.chargingSlots)
}
check sameCarShouldNotBePluggedAtDifferentChargingArea for 10

assert sameCarShouldNotBeParkedAtDifferentParkingArea {
	all disj p1, p2: ParkingArea | 
		(p1.parkedCars).ParkingSlot & (p2.parkedCars).ParkingSlot = none
}
check sameCarShouldNotBeParkedAtDifferentParkingArea for 10

// Bcz we assume disjoint sets
assert sameCarShouldNotBeParkedAndChargingAtSameTime {
	no (ParkingArea.parkedCars).ParkingSlot & 
	    (ChargingArea.chargingCars).ChargingSlot
}
check sameCarShouldNotBeParkedAndChargingAtSameTime for 10

assert carsParkedOrChargingAreNearbyThoseAreas {
	all c: Car | 
		c in ( (ParkingArea.parkedCars).ParkingSlot + 
			  (ChargingArea.chargingCars.ChargingSlot) )
		  implies
		  (c.carGpsVolume.gpsPoints & ParkingArea.areaGpsPoints != none)
}
check carsParkedOrChargingAreNearbyThoseAreas for 5

assert allParkingOrChargingCarsAreNotInUse {
	all c: Car | c.currentState = InUse implies
		c not in ( (ParkingArea.parkedCars).ParkingSlot + 
			      (ChargingArea.chargingCars).ChargingSlot)
}
check allParkingOrChargingCarsAreNotInUse for 10


/**
	PREDICATES/FUNCTIONS
*/
pred show() {
	all p: GpsPoint | p in Person.personGpsVolume.gpsPoints or p in CompanyArea.areaGpsPoints or
		p in Car.carGpsVolume.gpsPoints
	GpsVolume in (Person.personGpsVolume + Car.carGpsVolume)
	#GpsVolume > 1

	#Car > 0
	all c: Car | #c.carSeats < 3 and #c.damages < 2
	#Car.usedSeats > 0

	#Person > 0
	#(Person - User) > 0

	#CompanyArea > 0
	#(ParkingArea - ChargingArea) > 0

	#ParkingArea.parkedCars > 0
	#ChargingArea.chargingCars > 0
}
run show for 3
