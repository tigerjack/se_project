module Company
open Vehicles
open Areas
open Users

one sig Company {
	// Vehicles
	vehicles: set Vehicle,
	// operating areas
	parkingAreas: set ParkingArea,
	// registered users
	registeredUsers: set User
}

fact vehiclesMustBeOwnedByTheCompany {
	all v: Vehicle, c: Company | v in c.vehicles
}

fact parkingAreasShouldBelongToCompany {
	all p: ParkingArea, c: Company | p in c.parkingAreas
}

assert AllRegisteredUsersAreInCompanyUserSet {
	all u: User, c: Company | u in c.registeredUsers
}



pred show() {
	#Vehicle = 3
//	#ParkingArea > 0
//	#User > 0
	#GPSPoint = 0
}

run show for 15
// but 0 Fee, 0 FixedFee, 0 TimeFee, 10 Vehicle
