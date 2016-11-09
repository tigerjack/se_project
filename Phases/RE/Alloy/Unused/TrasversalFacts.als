module TrasversalFacts
open Cars
open Areas
open Users
open GPSUtilities
open BankingUtilities
open Company
open CarsUsage
open Cars


/**
	Trasversal Facts

fact noChargingVehicleInUse {
	all spa: SpecialParkingArea, u: RegisteredUser | 
		spa.chargingVehicles & u.usedVehicle = none
}





fun lookupByAddress[ad: Address]: set Car {
	all 
}

check AllRegisteredUsersAreInCompanyUserSet
*/
pred show() {
	#Car > 0
}

run show for 5 but 0 ReservationData, 0 Fee, 0 DrivingData
