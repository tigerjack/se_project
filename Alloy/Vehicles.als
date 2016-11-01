module Vehicles
open Utilities

/**
	Vehicles
*/
abstract sig Vehicle {
	code: Int,
	battery: one Battery,
	seats: Int,
	usedSeats: Int,
	currentPosition: one Position,
	currentState: one VehicleState
	// We assume there is one type of plug, so we don't mention it.
	// If multiple plugs should be allowed, we have to modify this sig
}
{code > 0 seats > 0 seats <=4 usedSeats <= seats}
fact codesAreUniques {
	all v1, v2: Vehicle | (v1 != v2) =>
		(v1.code != v2.code)
}

	// if vehicle state is used, than usedSeats > 0
	// if vehicle state is unused or unusable, than usedSeats = 0
	// if battery status is <= 0, current state is unusable}

sig Battery {
	statusPercentage: Int
}
// {statusPercentage >=0 statusPercentage <= 100}
fact batteryMustBeAssociatedToVehicle {
	all v: Vehicle, b: Battery | b in v.battery
}

sig Car extends Vehicle {}

abstract sig VehicleState {}
sig VehicleUsed extends VehicleState {}
sig VehicleUnused extends VehicleState {}
sig VehicleUnusable extends VehicleState {}
fact vehicleStateMustBeAssociatedToVehicle {
	all v: Vehicle, vs: VehicleState | vs in v.currentState
}

pred show() {}

run show for 5 but exactly 5 Vehicle, 5 Battery


