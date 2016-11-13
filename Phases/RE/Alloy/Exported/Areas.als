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
	areaPoints: some Point
}

sig ParkingArea extends CompanyArea {
	parkingSlots: set ParkingSlot,
	parkedCars: set Car
}
{
	#parkedCars <= #parkingSlots
}

sig ChargingArea extends ParkingArea {
	chargingSlots: some ChargingSlot,
	chargingCars: set Car
}
{	
	#chargingCars <= #chargingSlots
	#parkedCars <= #parkingSlots
	// A car can't be charging and parked at the same time
	// because the two sets are disjoint
	chargingCars & parkedCars = none
}

/**
	FACTS
*/
// Trivial
fact parkingSlotsAreaAssociatedToExactlyOneArea {
	all ps: ParkingSlot | one pa: ParkingArea | ps in pa.parkingSlots
}

fact chargingSlotsAreaAssociatedToExactlyOneArea {
	all cs: ChargingSlot | one ca: ChargingArea | cs in ca.chargingSlots
}

// Areas do not overlap
fact areaPositionsAreAssociatedToExaxtlyOneCompanyArea {
	all disj a1, a2: CompanyArea | a1.areaPoints & a2.areaPoints = none
}

// Parked Cars are in Parking Areas position
fact allParkedCarsAreInsideThoseAreaPositions {
	all pa: ParkingArea, c: Car | c in pa.parkedCars implies 
		c.carPoints in pa.areaPoints
}

//Charging Cars are in Charging Areas position
fact allChargingCarsAreInsideThoseAreaPositions {
	all ca: ChargingArea, c: Car | c in ca.chargingCars implies 
		c.carPoints in ca.areaPoints
}

// If a Car is inside an Area but not occupying a slot, it should be in use
fact allCarsInsideAreasButNotParkedOrChargingAreInUse {
	all c: Car |
		(c.carPoints in ParkingArea.areaPoints and 
		 c not in (ParkingArea.parkedCars + ChargingArea.chargingCars)) implies
		 c.currentState = InUse
}

// I.e. a ParkingArea has always a parkingCapacity > 0
fact parkingCapacityZeroCanOnlyBeAssociatedToChargingArea {
	all p: ParkingArea | p.parkingSlots = none implies 
		p in ChargingArea
}

// N.B. Implies and not Iff bcz a car in a ParkingArea can also be 
// Unavailable (or Plugged) in a ChargingArea
fact carStateAvailableOrReservedImpliesCarAtOneParkingArea {
	all c: Car, pa: ParkingArea, ca: ChargingArea | 
		(c.currentState = Available or c.currentState = Reserved) implies
		( (c in pa.parkedCars and c.carPoints in pa.areaPoints) or 
		  (c in ca.parkedCars and c.carPoints in ca.areaPoints) or 
		  (c in ca.chargingCars and c.carPoints in ca.areaPoints))
}

// If a car is plugged <=> it must be in one charging area
fact carStatePluggedIffCarInOneChargingCars {
	all c: Car | one ca: ChargingArea | 
		c.pluggedStatus = PluggedOn iff c in ca.chargingCars
}

fact carParkedInOneParkingArea {
	all pa1, pa2: ParkingArea | 
		(pa1 != pa2 implies 
			pa1.parkedCars & pa2.parkedCars = none)
}

fact carChargingInOneChargingArea {
	all ca1, ca2: ChargingArea | 
		(ca1 != ca2 implies 
			ca1.chargingCars & ca2.chargingCars = none)
}

/**
	ASSERTS
*/
assert areaPositionsAreNotOverlapping {
	all disj ca1, ca2: CompanyArea | ca1.areaPoints & ca2.areaPoints = none
}
check areaPositionsAreNotOverlapping for 10

assert sameCarShouldNotBePluggedAtDifferentChargingArea {
	all c: Car | one ca: ChargingArea | 
		c.pluggedStatus = PluggedOn iff
		c in ca.chargingCars
}
check sameCarShouldNotBePluggedAtDifferentChargingArea for 10

assert sameCarShouldNotBeParkedAtDifferentParkingArea {
	all disj p1, p2: ParkingArea | p1.parkedCars & p2.parkedCars = none
}
check sameCarShouldNotBeParkedAtDifferentParkingArea for 10

// Bcz we assume disjoint sets
assert sameCarShouldNotBeParkedAndChargingAtSameTime {
	no ParkingArea.parkedCars & ChargingArea.chargingCars
}
check sameCarShouldNotBeParkedAndChargingAtSameTime for 10

assert carsParkedOrChargingAreInsideThoseAreasPositions {
	all pa: ParkingArea, ca: ChargingArea | 
		(pa.parkedCars.carPoints in pa.areaPoints) and
		(ca.chargingCars.carPoints in ca.areaPoints)
}
check carsParkedOrChargingAreInsideThoseAreasPositions for 10

/**
	PREDICATES/FUNCTIONS
*/
pred show() {
	all p: Point | p in Person.personPoint or p in CompanyArea.areaPoints or
		p in Car.carPoints
}

run show for 3
