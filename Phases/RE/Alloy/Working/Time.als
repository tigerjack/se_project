module Time
open util/ordering[Time] as T0

sig Time {}

/*
abstract sig Event {
	pre, post: Time
}
{
	post = pre.next
}

fact EventTraces {
	all t: Time - T0/last | one e: Event | e.pre = t
}
*/
run {} for 5
