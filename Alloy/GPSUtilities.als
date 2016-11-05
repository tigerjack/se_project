module GPSUtilities

/**
	Geolocalization
*/

// A simple float used to describe a GPS latitude or longitude

sig GPSFloat {}

sig GPSPoint {
	latitude: one GPSFloat,
	longitude: one GPSFloat
}

sig GPSStraightLine {
	start: one GPSPoint,
	end: one GPSPoint
}
{start != end}

sig GPSPath {
	startLine: one GPSStraightLine,
	endLine: one GPSStraightLine,
	intermediateLines: set GPSStraightLine
}
{
	// No intermediate line is also a start or end line
	no x: intermediateLines | x = startLine or x = endLine
	// No intermediate line end point is equal to start line start point
	no x: intermediateLines | startLine.start = x.end

	// the start (end) of a start line should correspond to end (start) of
	// at most 1 intermediate line
	lone x: intermediateLines | startLine.end = x.start
	lone x: intermediateLines | startLine.start = x.end
	
	// Lines should be connected
	all x: intermediateLines | x.end = endLine.start 
		or one x1: intermediateLines | x.end = x1.start
	all x: intermediateLines | x.start = startLine.end 
		or one x1: intermediateLines | x.start = x1.end
	no intermediateLines implies (startLine = endLine 
		or startLine.end = endLine.start)
}

sig GPSPolygon extends GPSPath {}
// A polygon is a closed path
{	startLine.start = endLine.end}

// Note: it only checks start/end points, not intermediate points
pred lineIntersects(l1, l2: GPSStraightLine) {
	l1 != l2 and 
		(l1.start = l2.end or
		l1.end = l2.start or
		l1.end = l2.end or
		l1.end = l2.start)
}

pred pathsIntersects(p1, p2: GPSPath) {
	p1 != p2 and (some l1: p1.intermediateLines, l2: p2.intermediateLines | lineIntersects[l1, l2])
}

pred show() {}

run show for 5 but 3 GPSPolygon


