module Company
open Vehicles
open Areas
open Users
open Utilities

one sig Company {
	// Vehicles
	vehicles: set Vehicle,
	// operating areas
	operatingAreas: some OperatingArea,
	// registered users
	registeredUsers: some RegisteredUser
}

pred show() {}

run show for 5 but exactly 3 Vehicle

// but 0 Fee, 0 FixedFee, 0 TimeFee, 10 Vehicle
