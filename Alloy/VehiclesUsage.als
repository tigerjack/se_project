module VehiclesUsage
open Vehicles
open Users
open Utilities

sig DrivingData {
	user: one RegisteredUser,
	vehicle: one Vehicle
}

sig Reservation {
	timestamp: Int,
	user: one RegisteredUser
}
{timestamp > 0}


// Facts:
// if usedVehicle != 0, then the vehicle should have its state to Used
