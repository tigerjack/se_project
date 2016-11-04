module Areas
//open GPSUtilities
open Cars
open Codes

sig Address {}

abstract sig Area {
	code: one AreaCode,
	address: one Address,
// perimeter: one GPSPolygon
}
fact areaIdAndAddressAreUnique {
	all a1, a2: Area | a1 != a2 implies (a1.code != a2.code and
			a1.address != a2.address)
}
fact areaCodesAreAssociatedToOneArea
{
	all ac: AreaCode | one a: Area | ac in a.code
}

/*
	Parking areas are places where a user can park a vehicle
*/
sig ParkingArea extends Area {
	parkingCapacity: Int,
	parkedVehicles: set Car,
	metersForNearestChargingStation: Int	
}
{
	metersForNearestChargingStation > 0
	#parkedVehicles <= parkingCapacity
}

/*
	Special parking areas are places where a user can park a vehicle
	but also recharge the vehicle
*/
sig ChargingArea extends ParkingArea {
	sockets: some Socket,
	chargingVehicles: set Car
}
{	
	// Note that even a charging area stores the distance from the
	// nearest charging station
	#chargingVehicles <= #sockets
	#chargingVehicles + #parkedVehicles <= parkingCapacity
}

/*
	Operating areas are places where a user can pick a vehicle. 
	It is composed by all the parking areas and vehicles of this specific zone
*/
/*
sig OperatingArea extends Area {
	vehicles: set Vehicle, 
	parkingAreas: set ParkingArea
}

// If there is at least one vehicle, it should be at least one area to park

*/

/*
	It's a power supply. We assume there is one type of socket.
*/
sig Socket {}
fact socketMustBeAssociatedToOneChargingArea {
	all s: Socket | one ca: ChargingArea | s in ca.sockets
} 

pred show() {}

run show for 5


