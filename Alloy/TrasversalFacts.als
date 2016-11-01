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

fact vehiclesMustBeOwnedByTheCompany {
	all v: Vehicle, c: Company | v in c.vehicles
}

fact operatingAreasShouldBelongToCompany {
	all o: OperatingArea, c: Company | o in c.operatingAreas
}

assert AllRegisteredUsersAreInCompanyUserSet {
	all ru: RegisteredUser, c: Company | ru in c.registeredUsers
}

check AllRegisteredUsersAreInCompanyUserSet

pred show() {}

run show for 5 but 0 Reservation, 0 Fee, 0 DrivingData
