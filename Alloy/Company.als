module Company
open Cars
open Areas
open Users

one sig Company {
	// Vehicles
	cars: set Car,
	// parking areas
	parkingAreas: set ParkingArea,
	// registered users
	users: set User
}
{#cars > 0 implies #parkingAreas > 0}

fact vehiclesMustBeOwnedByTheCompany {
	all c: Car | one com: Company | c in com.cars
}

fact parkingAreasMustBelongToCompany {
	all p: ParkingArea | one com: Company |  p in com.parkingAreas
}

assert allUsersAreInCompanyUserSet {
	all u: User | one com: Company | u in com.users
}



pred show() {

	#Car = 3
	#ParkingArea > 0
/*
	#User > 0
	#GPSPoint = 0
*/
}

run show for 5 but 9 Int
// but 0 Fee, 0 FixedFee, 0 TimeFee, 10 Vehicle
