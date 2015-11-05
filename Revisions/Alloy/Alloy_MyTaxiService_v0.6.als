//////////////////////////////////////////////////////////////////////////////////////
//  																									
//  *MY TAXI SERVICE*																		
//  		*ALLOY	*																				
//  																									
//  SARA PISANI - LEONARDO TURCHI												
//  																						
//  POLITECNICO DI MILANO - AY 15/16											
//  SOFTWARE ENGINEERING 2														
//  																									
//////////////////////////////////////////////////////////////////////////////////////
// SIGNATURES > FACTS > PREDICATES - FUNCTIONS > ASSERTIONS
///////////////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
//SIGNATURES

///////////////////////////////////////////////////
//DATA TYPE - SIGNATURES
sig Integer{}
sig Strings{}
sig Date {}
sig Time {}
sig Boolean {}
	
sig Taxi{
	plate: one Strings,
	driver: one Strings,
	zone: one Zone,
	GPSCoord: one Strings
}

sig Queue{
	ID: one Integer,
	zone: one Zone, 
	taxiQueue: set Taxi
}

///////////////////////////////////////////////////
//ABSTRACT ENTITY - SIGNATURES

abstract sig User{
	ID: one Integer,
	eMail: one Strings,
	password: one Strings,
	name: one Strings,
	surname: one Strings,
	CF_ID: one Strings,
	birth: one Date,
	address: one Strings
}	

abstract sig Ride{
	startStreet: one Strings,
	stopStreet: one Strings,
	waitingTime: one Time,
	assignedTaxi: one Taxi,
	dateOfBooking: one Date,
	timeOfBooking: one Time
}	

abstract sig City{
	name: one Strings,
	region: one Strings,
	country: one Strings
}

///////////////////////////////////////////////////
//DEFINITION OF ABSTRACT ENTITY - SIGNATURES

sig Passenger extends User{
	payPalAccount: one Strings,
	simpleRide: lone Ride,
	bookedRidesList: set Ride
}

sig Driver extends User{
	licence: one Strings,
	availability : one Boolean,
	taxi: one Taxi
}

sig Zone extends City{
	cityName: one Strings,
	ZIPCode: one Integer,
	queue: one Queue
}

sig SharedRide extends Ride{
	sharers: set Passenger,
	} {
		#sharers <= 4
}

////////////////////////////////////////////////////////////////////////
//FACTS

// Impose a non empty User
fact noEmptyUser{
	all u: User | 
			   (#u.ID=1) 
		and (#u.eMail=1) 
		and (#u.password=1) 
		and (#u.name=1) 
		and (#u.surname=1) 
		and (#u.CF_ID=1) 
		and (#u.birth=1) 
		and (#u.address=1) 
}

// Impose a non empty Passenger
fact noEmptyPassenger{
	all p: Passenger | (#p.payPalAccount=1)
}

// Impose a non empty Driver 
fact noEmptyDriver{
	all d: Driver | (#d.licence=1) and (#d.availability=1) and (#d.taxi=1)
}

// Impose a non empty Taxi
fact noEmptyTaxi{
	all t: Taxi | (#t.plate=1) and (#t.driver=1) and (#t.zone=1) and (#t.GPSCoord=1)
}

// Impose a non empty City 
fact noEmptyCity{
	all c: City | (#c.name=1) and (#c.region=1) and (#c.country=1)
}

// Impose a non empty Zone 
fact noEmptyZone{
	all z: Zone | (#z.name=1) and (#z.ZIPCode=1) and (#z.queue=1)
}

// Impose a non empty Queue
fact noEmptyQueue{ 
	all q: Queue | (#q.ID=1) and (#q.zone=1) and (#q.taxiQueue=1)
}

// Impose a non empty Ride
fact noEmptyRide{
	all r: Ride | (#r.startStreet=1) and (#r.stopStreet=1) and (#r.waitingTime=1) and (#r.assignedTaxi=1)
}

// Impose a non empty SharedRide
fact noEmptySharedRide{	
	all s: SharedRide | (#s.sharers=1) 
}

// Impose no duplicate mail and no duplicate ID
fact noDuplicateUser{
	no disj u1, u2: User | (u1.eMail = u2.eMail) and (u1.ID = u2.ID)
}

// Impose no duplicate payPal account
fact noDuplicatePassenger{
	no disj p1,p2: Passenger | (p1.payPalAccount = p2.payPalAccount)
}

// Impose no duplicate licence
fact noDuplicateDriver{
	no disj d1,d2: Driver | (d1.licence = d2.licence)
}

// Impose no duplicate plate
fact noDuplicateTaxi{
	no disj t1, t2: Taxi | (t1.plate = t2.plate)
}

// Impose no duplicate ZIPCode and Queue
fact noDuplicateZone{
	no disj z1,z2: Zone | (z1.ZIPCode = z2.ZIPCode) and (z1.queue = z2.queue)
}

// Impose no duplicate ID, zone and taxiQueue
fact noDuplicateQueue{
	no disj q1,q2: Queue | (q1.ID = q2.ID) and (q1.zone = q2.zone) and (q1.taxiQueue = q2.taxiQueue)
}

// Impose that cannot be deleted a not simple booked ride
fact noInexistentSimpleRideDeletion{
	all r: Ride, p: Passenger | 
										(
											(
												(#r.dateOfBooking = 0) or (#r.timeOfBooking = 0) 
											)
											and
											(
												(#r.startStreet = 0) or (#r.stopStreet = 0)
											)
											implies (p.simpleRide not in r)
										)
}

// Impose that cannot be deleted a not booked ride
fact noInexistentBookedRideDeletion{
	all r: Ride, p: Passenger | 
										(
											(
												(#r.dateOfBooking = 0) or (#r.timeOfBooking = 0) 
											)
											and
											(
												(#r.startStreet = 0) or (#r.stopStreet = 0)
											)
											implies (p.bookedRidesList not in r)
										) 
}

// Impose that only registered user can book a ride
fact noUnregisteredUserMakeRequests{
	all p: Passenger | (#p.ID = 0) implies (#p.simpleRide = 0 and #p.bookedRidesList = 0)
}

////////////////////////////////////////////////////////////////////////
//PREDICATES - FUNCTIONS

//Show a world in which there are following rules
pred show(){
	#User=1
	#Taxi=1
	#Ride=1
	#City=1
}
run show for 1

//Show a world in which there is a booked ride
pred showBookedRide(){
	//all r : Ride | (r.startStreet= "viale Gran Sasso 10") and (r.stopStreet= "viale Romagna 60")	  <<<<<<<<<<<<
}
run showBookedRide for 1

//Show a world in which there is a driver confirming ride
pred showDriverAcceptingRide(){
	all r: Ride, d: Driver | (r.assignedTaxi = d.taxi)
}
run showDriverAcceptingRide for 1

//Predicate for a new ride request
pred rideRequest(r:Ride, p1,p2: Passenger){
	r not in p1.simpleRide implies p2.simpleRide = p1.simpleRide+r	
}
run rideRequest for 1

//Predicate for a new ride booking request
pred rideBookingRequest(r:Ride, p1,p2: Passenger){
	r not in p1.bookedRidesList implies p2.bookedRidesList = p1.bookedRidesList+r
}
run rideBookingRequest for 1

//Predicate for a ride deletion
pred deleteRideRequest(r:Ride, p1,p2: Passenger){
	r in p1.simpleRide implies p2.simpleRide = p1.simpleRide-r
}
run deleteRideRequest for 1

//Predicate for a booked ride deletion
pred deleteBookingRideRequest(r:Ride, p1,p2: Passenger){
	r in p1.bookedRidesList implies p2.bookedRidesList = p1.bookedRidesList-r
}
run deleteBookingRideRequest for 1


////////////////////////////////////////////////////////////////////////
//ASSERTIONS

//Check that there cannot exist a ride without a taxi
assert noRideWithoutTaxi{
	no r: Ride | (no t: Taxi | r.assignedTaxi = t)
}
check noRideWithoutTaxi

//Check that there cannot exist a ride without a user
assert noRideWithoutUser{
	all p: Passenger |(#p.payPalAccount=0) implies (#p.simpleRide=0) and (#p.bookedRidesList =0)
}
check noRideWithoutUser

//Check that there cannot exist a duplicate ride
assert noDuplicateRide{
		
		
		
		/*iff

		//two NOT equal rides
		not
		(
			r1.startStreet = r2.startStreet 	and r1.stopStreet  = r2.stopStreet 
			and 
			r1.dateOfBooking = r2.dateOfBooking and 	r1.timeOfBooking = r2.timeOfBooking 
		)
*/

/*
	all r1, r2: SharedRide, p1, p2: Passenger | 
	(
		//two equal rides
		(
			r1.startStreet = r2.startStreet 	and r1.stopStreet  = r2.stopStreet 
			and 
			r1.dateOfBooking = r2.dateOfBooking and 	r1.timeOfBooking = r2.timeOfBooking 
		)

		implies

		(

			r1.sharers != r2.sharers
			
			or

			(
				//different passengers
				(
					r1 in p1.bookedRidesList
					or
					r1 in p1.simpleRide
				)
				and
				(
					r2 in p2.bookedRidesList
					or
					r2 in p2.simpleRide
				)
			)
		)
	) 
*/
}
check noDuplicateRide

//Check the deletion for simple ride event predicate
assert deleteRideEvent{
	all r1: Ride, p1, p2: Passenger | 
		(
			(
				p1.simpleRide = r1
				and
				p2.simpleRide = r1
				and
				deleteRideRequest[r1,p1,p2]
			)	
			implies
			(
				p1.simpleRide not in r1
			)
		)
}
check deleteRideEvent

//Check the deletion for booking ride event predicate
assert deleteRideBookingEvent{
	all r1: Ride, p1, p2: Passenger | 
		(
			(
				p1.bookedRidesList = r1
				and
				p2.bookedRidesList = r1
				and
				deleteBookingRideRequest[r1,p1,p2]
			)	
			implies
			(
				p1.bookedRidesList != r1
			)
		)
}
check deleteRideBookingEvent

//Check the simple ride request predicate 
assert newRideEvent{

}
check newRideEvent

//Check the ride booking request predicate 
assert newRideBookingEvent{

}
check newRideBookingEvent

//Check that a new user is added
assert newUserRegistrationSuccess{

}
check newUserRegistrationSuccess

//Check that there aren't two equal users
assert noDuplicateUser{
no disj u1, u2 : User |  (u1.ID=u2.ID) and (u1.eMail=u2.eMail) and
							(u1.password=u2.password) and (u1.name=u2.name) and
							(u1.surname=u2.surname) and (u1.CF_ID=u2.CF_ID) and
							(u1.birth=u2.birth) and (u1.address=u2.address)		
}
check noDuplicateUser

//Check that there aren't two equal drivers
assert noDuplicateDrivers{
 no disj d1,d2: Driver |  (d1.licence=d2.licence) and (d1.availability=d2.availability) and (d1.taxi=d2.taxi)						
}
check noDuplicateDrivers

//Check that cannot exist a passenger without a paypal account
assert noPassengerWithoutPaypal{
no p: Passenger | (#p.payPalAccount =0)
}
check noPassengerWithoutPaypal

//Check that cannot exist a passenger without a CF_ID
assert noPassengerWithoutCF{
no p: Passenger | (#p.CF_ID=0)
}
check noPassengerWithoutCF

//Check that cannot exist a ride without a destination or departure address
assert noRideWithoutDepDesAddress{
no r: Ride | (#r.startStreet =0) and (#r.stopStreet =0)
}
check noRideWithoutDepDesAddress

//Check that in a shared ride cannot be reserved more than 4 seats
assert noTaxiOverbooking{
no s: SharedRide | #s.sharers > 4
}
check noTaxiOverbooking

