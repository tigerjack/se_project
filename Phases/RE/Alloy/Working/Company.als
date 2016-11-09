module Company
open Cars
open Areas
open Users
open CarsUsageFunctions

/**
	SIGNATURES
*/
one sig Company {
	// Vehicles
	cars: some Car,
	// parking areas
	parkingAreas: some ParkingArea,
	// registered users
	users: set User,
	carsUsageData: set CarsUsageData
}
// If there is a car owned by the company, there is also a parking area
// to leave the car
{#cars > 0 implies #ChargingArea > 0}

/**
	FACTS
*/
fact vehiclesMustBeOwnedByTheCompany {
	all c: Car | one com: Company | c in com.cars
}
fact parkingAreasMustBelongToCompany {
	all p: ParkingArea | one com: Company |  p in com.parkingAreas
}
fact allUsersAreInCompanyUserSet {
	all u: User | one com: Company | u in com.users
}

/**
	ASSERTS
*/
assert allUsersAreInCompanyUserSet {
	all u: User | one com: Company | u in com.users
}

check allUsersAreInCompanyUserSet for 3 but 8 Int


/**
	PREDICATES/FUNCTIONS
*/
pred show() {

	#Car > 2
	#ParkingArea > 2
	#User > 0
/*
	#GPSPoint = 0
*/
}

run show for 5 but 8 Int
// but 0 Fee, 0 FixedFee, 0 TimeFee, 10 Vehicle
