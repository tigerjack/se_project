module CarUsageFunctions
open Cars
open Persons
open Time
//open Areas

/**
	The main problem here is that, introducing a dynamic behavior, we should
	introduce the concept of time for all other entities. F.e., in our world, a 
	Car can only be in one given state
*/

/**
	SIGNATURES
*/
abstract sig CarUsageTimes {
	timeDatas: (User lone -> lone Car ) -> Time
}

one sig ReservationDataStartTime extends CarUsageTimes {}
{
	all t: Time |
		User.(timeDatas.t).currentState - Reserved = none
}

one sig UsingDataStartTime extends CarUsageTimes {}
{
	all t: Time |
		User.(timeDatas.t).currentState - InUse = none
}


fact ifAUserIsInUsingSetItCantBeInReservedSetAndViceversa {
	no
	  (ReservationDataStartTime.timeDatas.Time).Car &
	  (UsingDataStartTime.timeDatas.Time).Car	
}

fact usersCantBeInReservingAndUsingCarDatas {
	no User.(UsingDataStartTime.timeDatas.Time) &
		  User.(ReservationDataStartTime.timeDatas.Time)
}

fact oneUserOneCarForEachSet {
	all cut: CarUsageTimes, u: User, c: Car |
		lone (cut.timeDatas.Time).c and
		lone u.(cut.timeDatas.Time)
}

fact anUserCanBeInOnlyOneCarUsageTimes { 
	all u: User | all disj t1, t2: Time  | 
		no u.(CarUsageTimes.timeDatas.t1) & 
		      u.(CarUsageTimes.timeDatas.t2)
}

fact aCarCanBeInOnlyOneCarUsageTimes { 
	all c: Car | all disj t1, t2: Time |
		no (CarUsageTimes.timeDatas.t1).c & 
		      (CarUsageTimes.timeDatas.t2).c
}

fact ifACarIsInUsingSetItCantBeInReservedSetAndViceversa {
	 no
	  User.(ReservationDataStartTime.timeDatas.Time) &
	  User.(UsingDataStartTime.timeDatas.Time)
}


///////////
fact carsInUseInUsingDataStartTime {
	all c: Car, t: Time |
		c.currentState = InUse iff
		c in User.(UsingDataStartTime.timeDatas.t)  
}

fact carsReservedInReservationDataStartTime {
	all c: Car, t: Time | 
		c in User.(ReservationDataStartTime.timeDatas.t) iff 
		c.currentState = Reserved
}
/**
	ASSERTS
*/

assert aCarInOnlyOneSet {
	all c: Car | all disj cut1, cut2: CarUsageTimes |
		no (cut1.timeDatas.Time).c & (cut2.timeDatas.Time).c
}
check aCarInOnlyOneSet for 5

assert aUserInOnlyOneSet {
	all u: User | all disj cut1, cut2: CarUsageTimes |
		no u.(cut1.timeDatas.Time) & u.(cut2.timeDatas.Time)
}
check aUserInOnlyOneSet for 5

/**
	PREDICATES
*/
pred show() {
	#User > 1
	#Car > 1
	#User.(ReservationDataStartTime.timeDatas.Time) > 2
	#(ReservationDataStartTime.timeDatas.Time).Car > 2
	#User.(UsingDataStartTime.timeDatas.Time) > 2
	#(UsingDataStartTime.timeDatas.Time).Car > 2
	#InUse > 0
	#Reserved > 0

}
run show for 10

pred init() {
	no (ReservationDataStartTime.timeDatas).first and
	no (UsingDataStartTime.timeDatas).first
}
run init for 2

/*


pred canReserveACar[u: User, c: Car, t: Time] {
	c.currentState = Available and
//	u not in Car.usedSeats and
//	u not in DrivingCarStartTime.drivingDatas.t.Car and 
	no u.((ReservationDataStartTime.timeDatas).t) and
	no ((ReservationDataStartTime.timeDatas).t).c
}
run canReserveACar for 3

pred reserveACar[u: User, c: Car, t: Time, r, r': ReservationDataStartTime] {
//	canReserveACar[u, c, t] and
	r'.timeDatas = r.timeDatas + (u -> c) -> t
}
run reserveACar for 3
*/

