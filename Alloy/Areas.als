module Areas
//open GPSUtilities
open Cars

sig Address {}


abstract sig CompanyArea {
//	code: one AreaCode,
	address: one Address,
// perimeter: one GPSPolygon
}

sig ParkingArea extends CompanyArea {
	parkingCapacity: Int,
	parkedCars: set Car,
//	metersForNearestChargingStation: Int	
}
{
//	metersForNearestChargingStation > 0
	parkingCapacity >= 0
	#parkedCars <= parkingCapacity
}

sig ChargingArea extends ParkingArea {
	chargingCapacity: Int,
	chargingCars: set Car
}
{	
	// Note that even a charging area stores the distance from the
	// nearest charging station
	chargingCapacity > 0
	#chargingCars <= chargingCapacity
	#chargingCars + #parkedCars <= parkingCapacity
	//A car can't be charging and parked at the same time
	chargingCars & parkedCars = none
}


// FACT
// Maybe redundant, see next fact
fact areaAddressesAreUnique {
	all a1, a2: CompanyArea | a1 != a2 implies 
		a1.address != a2.address
}

fact areaAddressesAreAssociatedToExaxtlyOneCompanyArea {
	all a: Address | one ar: CompanyArea | a in ar.address
}

fact parkingCapacityZeroCanOnlyBeAssociatedToChargingArea {
	all p: ParkingArea | p.parkingCapacity = 0 implies 
		p in ChargingArea
}

// N.B. Implies and not Iff bcz a car in a ParkingArea can also be 
// Unavailable (or Plugged in a ChargingArea
fact carStateAvailableOrReservedImpliesCarAtOneParkingArea {
	all c: Car, pa: ParkingArea, ca: ChargingArea | 
		(c.currentState = Available or c.currentState = Reserved) implies
		(c in pa.parkedCars or 
		c in ca.parkedCars or 
		c in ca.chargingCars)
}


fact carStateInUseImpliesCarNotInParkingArea {
	all c: Car, pa: ParkingArea, ca: ChargingArea |
		c.currentState = InUse implies
		(c not in pa.parkedCars and c not in ca.chargingCars)
}

// If a car is plugged <=> it must be in one charging area
fact carStatePluggedIffCarInOneChargingCars {
	all c: Car | one ca: ChargingArea | 
		c.currentState = Plugged iff c in ca.chargingCars
}


fact carParkedInOneParkingArea {
	all pa1, pa2: ParkingArea | 
		(pa1 != pa2 implies 
		pa1.parkedCars & pa2.parkedCars = none) and
		(ParkingArea.parkedCars & ChargingArea.chargingCars) = none
}


/*
	all c: Car | some pa1, pa2: ParkingArea | 
		(c in pa1.chargingCars and 
		c in pa2.chargingCars) implies pa1 = pa2
*/


// ASSERT
assert sameCarShouldNotBePluggedAtDifferentChargingArea {
	all c: Car | one ca: ChargingArea | 
		c.currentState = Plugged implies
		c in ca.chargingCars
}

check sameCarShouldNotBePluggedAtDifferentChargingArea for 5 but 8 Int

// PREDICATES
pred show() {
	#Car > 0 
	#ChargingArea > 0
	#ParkingArea - #ChargingArea > 0
	#Battery.statusPercentage = #Car
	#ChargingArea.chargingCars > 0
	#ParkingArea.parkedCars - #ChargingArea.parkedCars > 0
	#Damage = 1
	1 in Car.usedSeats
	0 in Battery.statusPercentage
	19 in Battery.statusPercentage
	20 in Battery.statusPercentage
}

run show for 5 but 8 Int


/*
	Operating areas are places where a user can pick a vehicle. 
	It is composed by all the parking areas and vehicles of this specific zone
*/
/*
sig Socket {}
sig AreaCode extends Code {}

sig OperatingArea extends Area {
	vehicles: set Vehicle, 
	parkingAreas: set ParkingArea
}

fact areaCodesAreAssociatedToOneArea
{
	all ac: AreaCode | one a: Area | ac in a.code
}

fact socketMustBeAssociatedToOneChargingArea {
	all s: Socket | one ca: ChargingArea | s in ca.sockets
}
*/
