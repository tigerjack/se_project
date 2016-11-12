module CarUsageFunctions
open Cars
open Persons
open BankingFunctions

/**
	SIGNATURES
*/
abstract sig CarsUsageData {}
abstract sig CarsUsageDataSet {}

sig Minute {}

one sig DrivingDatas extends CarsUsageDataSet {
	dataset: User lone -> lone DrivingData
}

sig DrivingData extends CarsUsageData {
	isDriving: User lone -> lone Car,
//	car: one Car,
	// The minutes passed from the driving start
	ridingMinutes: seq Minute,
	// The range of minutes in which there is a passenger in the car
	passengersAtTimeT: set Person,
	currentTimeFee: one TimeFee
}
{
	#ridingMinutes > 0
	#passengers < #car.availableSeats
	
}

sig ReservationData extends CarsUsageData {
	hasReserved: User lone -> lone Car,
	// The time passed from the reservation start
	reservationMinutes: Int
}
{
	reservationMinutes > 0 and reservationMinutes <= 60
}

sig PluggingData {
}

sig EndingRideData {
}

fact allDrivingDataInDrivingDatas {
	all d: DrivingData | d in DrivingDatas.dataset
}

/**
	PREDICATES
*/
pred canReserveACar[u: User, c: Car] {
	
}

pred show() {}

run show for 3
