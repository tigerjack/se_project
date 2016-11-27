module GeoUtilities

sig GpsPoint {}

sig GpsVolume {
	gpsPoints: some GpsPoint
}

fact differentGpsVolumeShouldDifferForAtLeastOnePoint {
	all disj gv1, gv2: GpsVolume | 
		(gv1.gpsPoints + gv2.gpsPoints) -
		(gv1.gpsPoints & gv2.gpsPoints) != none
}

pred show() {
	#GpsVolume > 1
}
run show for 5
