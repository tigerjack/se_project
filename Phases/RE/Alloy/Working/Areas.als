module Areas
open Cars
open GeoUtilities

/**
	SIGNATURES
*/
abstract sig CompanyCarSlot {}
sig ParkingSlot, ChargingSlot extends CompanyCarSlot {}

abstract sig CompanyArea {
	positions: some Position
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
	// bcz the two sets are disjoint
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
//	all p: Position | one ar: CompanyArea | p in ar.positions
	all disj a1, a2: CompanyArea | a1.positions & a2.positions = none
}

// Parked/Charging Cars in Areas position
fact allParkedCarsAreInsideThoseAreaPositions {
	all pa: ParkingArea, c: Car | c in pa.parkedCars implies 
		c.carPosition in pa.positions
}

fact allChargingCarsAreInsideThoseAreaPositions {
	all ca: ChargingArea, c: Car | c in ca.chargingCars implies 
		c.carPosition in ca.positions
}

fact allCarsInsideAreasButNotParkedOrChargingAreInUse {
	all c: Car |
		(c.carPosition in ParkingArea.positions and 
		 c not in (ParkingArea.parkedCars + ChargingArea.chargingCars)) implies
		 c.currentState = InUse
}

// I.e. a ParkingArea has always a parkingCapacity > 0
fact parkingCapacityZeroCanOnlyBeAssociatedToChargingArea {
	all p: ParkingArea | p.parkingSlots = none implies 
		p in ChargingArea
}

// N.B. Implies and not Iff bcz a car in a ParkingArea can also be 
// Unavailable (or Plugged in a ChargingArea
fact carStateAvailableOrReservedImpliesCarAtOneParkingArea {
	all c: Car, pa: ParkingArea, ca: ChargingArea | 
		(c.currentState = Available or c.currentState = Reserved) implies
		( (c in pa.parkedCars and c.carPosition in pa.positions) or 
		  (c in ca.parkedCars and c.carPosition in ca.positions) or 
		  (c in ca.chargingCars and c.carPosition in ca.positions))
}

fact carStateInUseImpliesPositionDifferentFromParkingArea {
	all c: Car, pa: ParkingArea | c.currentState = InUse implies 
		c.carPosition not in pa.positions
}

fact carStateInUseImpliesCarNotInParkingOrChargingArea {
	all c: Car, pa: ParkingArea, ca: ChargingArea |
		c.currentState = InUse implies
		(c not in pa.parkedCars and c not in ca.chargingCars)
}

// If a car is plugged <=> it must be in one charging area
fact carStatePluggedIffCarInOneChargingCars {
	all c: Car | one ca: ChargingArea | 
		c.pluggedStatus = PluggedOn iff c in ca.chargingCars
}

fact carParkedInOneParkingArea {
	all pa1, pa2: ParkingArea | 
		(pa1 != pa2 implies 
		pa1.parkedCars & pa2.parkedCars = none) and
		(ParkingArea.parkedCars & ChargingArea.chargingCars) = none
}

/**
	ASSERTS
*/
assert areaPositionsAreNotOverlapping {
	all disj ca1, ca2: CompanyArea | ca1.positions & ca2.positions = none
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
	ParkingArea.parkedCars & ChargingArea.chargingCars = none
}
check sameCarShouldNotBeParkedAndChargingAtSameTime for 10

assert carsParkedOrChargingAreInsideThoseAreasPositions {
	all pa: ParkingArea, ca: ChargingArea | 
		(pa.parkedCars.carPosition in pa.positions) and
		(ca.chargingCars.carPosition in ca.positions)
}
check carsParkedOrChargingAreInsideThoseAreasPositions for 10

/**
	PREDICATES/FUNCTIONS
*/
pred show() {
//	#ChargingArea > 0
//	#(ParkingArea - ChargingArea) > 0
	#Car > 0
//	#InUse > 0
}

run show for 3
