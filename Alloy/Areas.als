module Areas
open Utilities
open Vehicles
/**
	Geographical Areas
*/
abstract sig Area {
	// Replace this ...
	// bounds: seq Position
	// ... with the correct formulation of this
	startPosition: one Position,
	intermediatePositions: set Position,
	endPosition: one Position
}
{
	no x: intermediatePositions | startPosition=x or endPosition=x
}

/*
	Parking areas are places where a user can park a vehicle
*/
sig ParkingArea extends Area {
	parkingCapacity: Int,
	parkedVehicles: set Vehicle	
}
{#parkedVehicles <= parkingCapacity}

/*
	Special parking areas are places where a user can park a vehicle
	but also recharge the vehicle
*/
sig SpecialParkingArea extends ParkingArea {
	sockets: some Socket,
	chargingVehicles: set Vehicle
}
// ?? check
{#chargingVehicles <= #plugs
	and	
 #chargingVehicles + #parkedVehicles <= parkingCapacity
}

/*
	Operating areas are places where a user can pick a vehicle. 
	It is composed by all the parking areas and vehicles of this specific zone
*/
sig OperatingArea extends Area {
	vehicles: set Vehicle, 
	parkingAreas: set ParkingArea
}
// If there is at least one vehicle, it should be at least one area to park
{#vehicles > 0 => #parkingAreas > 0}


/*
	It's a power supply. We assume there is one type of socket.
*/
sig Socket {}
fact socketMustBeAssociatedToSpecialParkingStation {
	all spa: SpecialParkingArea, s: Socket | s in spa.sockets
}

pred show() {}

run show for 5


