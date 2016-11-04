module TrasversalFacts
open Vehicles
open Areas
open Users
open Utilities
open Company
open VehiclesUsage


/**
	Trasversal Facts

fact noChargingVehicleInUse {
	all spa: SpecialParkingArea, u: RegisteredUser | 
		spa.chargingVehicles & u.usedVehicle = none
}
*/




fun lookupByAddress[ad: Address]: set Car {
	all 
}

check AllRegisteredUsersAreInCompanyUserSet

pred show() {}

run show for 5 but 0 Reservation, 0 Fee, 0 DrivingData
