module Vehicles
//open GPSUtilities
/**
	Vehicles
*/
abstract sig Vehicle {
	code: Int,
	battery: one Battery,
	seats: Int,
	usedSeats: Int,
//	currentPosition: one GPSPoint,
	currentState: one VehicleState
	// We assume there is one tye of plug, so we don't mention it.
	// If multiple plugs should be allowed, we have to modify this sig
}
{
	currentState != none
	code > 0 
	seats > 0 and seats <=4 
	usedSeats >= 0 and usedSeats <= seats
	currentState = InUse implies usedSeats > 0
	currentState != InUse implies usedSeats = 0
	// if vehicle state is used, than usedSeats > 0
	// if vehicle state is unused or unusable, than usedSeats = 0
	// if battery status is <= 0, current state is unusable}

	
}
fact codesAreUniques {
	all v1, v2: Vehicle | (v1 != v2) =>
		(v1.code != v2.code)
}


sig Car extends Vehicle {}

sig Battery {
	statusPercentage: Int
}
/*WTF: It doesn't work!!
{
	statusPercentage >= 0 statusPercentage <= 100
}
*/
fact batteryMustBeAssociatedToVehicle {
	all v: Vehicle, b: Battery | b in v.battery
}


enum VehicleState {
	InUse, Available, Reserved, Unavailable, Plugged
}

/*
sig VehicleUsed extends VehicleState {}
sig VehicleUnused extends VehicleState {}
sig VehicleUnusable extends VehicleState {}
fact vehicleStateMustBeAssociatedToVehicle {
	all v: Vehicle, vs: VehicleState | vs in v.currentState
}
*/
pred show() {}

run show for 5


