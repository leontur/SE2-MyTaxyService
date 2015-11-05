////////////////////////////////////////////////////////////////////////
//  																									 //
//  MY TAXI SERVICE																			 //
//  ALLOY																							 //
//  																									 //
//  SARA PISANI - LEONARDO TURCHI													 //
//  																									 //
//  POLITECNICO DI MILANO - AY 15/16												 //
//  SOFTWARE ENGINEERING 2															 //
//  																									 //
////////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////////
//SIGNATURES

///////////////////////////////////////////////////
//DATA TYPE - SIGNATURES
sig Integer{}
sig Strings{}
sig Date {}
sig Time {}
sig Boolean {}


sig Passenger extends User{
	payPalAccount: one Strings,
	ridesList: set Ride
}
sig Driver extends User{
	licence: one Strings,
	availability : one Boolean,
	taxi: one Taxi
}
sig Taxi{
	plate: one Strings,
	driver: one Strings,
	zone: one Zone,
	GPSCoord: one Strings
}

sig Zone{
	name: one Strings,
	ZIPCode: one Integer,
	queue: one Queue
}
sig Queue{ 
	ID: one Integer,
	zone: one Zone, 
	taxiQueue: set Taxi
}	

sig SharedRide extends Ride{
	sharers: set Passenger,
	} {
		#sharers <= 4
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
	assignedTaxi: one Taxi
}	

abstract sig City{
	name: one Strings,
	region: one Strings,
	country: one Strings
}


///////////////////////////////////////////////////
//DEFINITION OF ABSTRACT ENTITY - SIGNATURES




////////////////////////////////////////////////////////////////////////
//FACTS

fact noEmptyUser{
	// Impose a non empty User
	all u: User | (#u.ID=1) and (#u.eMail=1) and (#u.password=1) and (#u.name=1) and (#u.surname=1) and (#u.CF_ID=1) and (#u.birth=1) and (#u.address=1) 
}

fact noEmptyPassenger{
	// Impose a non empty Passenger
	all p: Passenger | (#p.payPalAccount=1)
}

fact noEmptyDriver{
	// Impose a non empty Driver 
	all d: Driver | (#d.licence=1) and (#d.availability=1) and (#d.taxi=1)
}

fact noEmptyTaxi{
	// Impose a non empty Taxi
	all t: Taxi | (#t.plate=1) and (#t.driver=1) and (#t.zone=1) and (#t.GPSCoord=1)
}

fact noEmptyCity{
	// Impose a non empty City 
	all c: City | (#c.name=1) and (#c.region=1) and (#c.country=1)
}

fact noEmptyZone{
	// Impose a non empty Zone 
	all z: Zone | (#z.name=1) and (#z.ZIPCode=1) and (#z.queue=1)
}

fact noEmptyQueue{
	// Impose a non empty Queue 
	all q: Queue | (#q.ID=1) and (#q.zone=1) and (#q.taxiQueue=1)
}

fact noEmptyRide{
	// Impose a non empty Ride
	all r: Ride | (#r.startStreet=1) and (#r.stopStreet=1) and (#r.waitingTime=1) and (#r.assignedTaxi=1)
}

fact noEmptySharedRide{
	// Impose a non empty SharedRide
	all s: SharedRide | (#s.sharers=1) 
}

fact noDuplicateUser{
	// Impose no duplicate mail and no duplicate ID
	no disj u1, u2: User | (u1.eMail = u2.eMail) and (u1.ID = u2.ID)
}

fact noDuplicatePassenger{
	// Impose no duplicate payPal account
	no disj p1,p2: Passenger | (p1.payPalAccount = p2.payPalAccount)
}

fact noDuplicateDriver{
	// Impose no duplicate licence
	no disj d1,d2: Driver | (d1.licence = d2.licence)
}

fact noDuplicateTaxi{
	// Impose no duplicate plate
	no disj t1, t2: Taxi | (t1.plate = t2.plate)
}

fact noDuplicateZone{
	// Impose no duplicate ZIPCode and Queue
	no disj z1,z2: Zone | (z1.ZIPCode = z2.ZIPCode) and (z1.queue = z2.queue)
}

fact noDuplicateQueue{
	// Impose no duplicate ID, zone and taxiQueue
	no disj q1,q2: Queue | (q1.ID = q2.ID) and (q1.zone = q2.zone) and (q1.taxiQueue = q2.taxiQueue)
}


////////////////////////////////////////////////////////////////////////
//PREDICATES


////////////////////////////////////////////////////////////////////////
//FUNCTIONS


////////////////////////////////////////////////////////////////////////
//ASSERTIONS

assert NoRideWithoutTaxi{
	//Check that there can't be ride without an owner
	no t: Taxi | (no r: Ride | r.assignedTaxi = t)
}
	check NoRideWithoutTaxi


////////////////////////////////////////////////////////////////////////
//COMMANDS











