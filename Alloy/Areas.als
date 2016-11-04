module Areas
//open GPSUtilities
open Vehicles

/**
	Geographical Areas
*/
abstract sig Area {
	id: one Int,
	address: one String,
	// perimeter: one GPSPolygon
}
fact areaIdDoNotOverlap {
	all a1, a2: Area | a1 != a2 implies (a1.id != a2.id and
			a1.address != a2.address)
}

/*
	Parking areas are places where a user can park a vehicle
*/
sig ParkingArea extends Area {
	parkingCapacity: Int,
	parkedVehicles: set Vehicle,
	metersForNearestChargingStation: Int	
}
{
	#metersForNearestChargingStation > 0
	#parkedVehicles <= parkingCapacity
}

/*
	Special parking areas are places where a user can park a vehicle
	but also recharge the vehicle
*/
sig ChargingArea extends ParkingArea {
	sockets: some Socket,
	chargingVehicles: set Vehicle
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
{#vehicles > 0 => #parkingAreas > 0}
*/

/*
	It's a power supply. We assume there is one type of socket.
*/
sig Socket {}
fact socketMustBeAssociatedToSpecialParkingStation {
	all ca: ChargingArea, s: Socket | s in ca.sockets
}

pred show() {}

run show for 5


