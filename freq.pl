#!/usr/bin/perl -w -CS
#
#
# freq.pl 
# 
#
use strict;

use Text::CSV_XS;
use Getopt::Long;

my $arguments = join ' ', $0, @ARGV;
my $nbin;
my $maxid = 1000000000000000000000;
my $id_var_name = "VisitNumber";
my $id_var_no = 1;
my $help = 0;
my $warn = 0;
my $crossed_var;
my $idf = 1;
my $xsv = "Upc";
my $ofile;
my $counter;
my @double_crossed;
my $chop_max = 0;
my $count_two = 0;
my $tvn;
my $vfile;
my $use_stemmer = 0;
my $novarprint = 0;
my $weight_file;
my $weight_function = 0;
my $debug = 0;
my $noheader = 0;

my $oresult = GetOptions( 'maxid=i' => \$maxid,  'idf=i' => \$idf,  'sv=s' => \$xsv,
	'warn+' => \$warn, 'h+' => \$help,  'ofile=s' => \$ofile,
	'id_var_name=s' => \$id_var_name, 'counter=s' => \$counter,
	'double_crossed=s' => \@double_crossed, 'chop_max+' => \$chop_max, 'count_two+' => \$count_two,
	'tvn=s' => \$tvn, 'vfile=s' => \$vfile, 'stem+' => \$use_stemmer, 'novarprint+' => \$novarprint,
	'weight_file=s' => \$weight_file, 'weight_function=i' => \$weight_function, 'debug+' => \$debug,
	'noheader+' => \$noheader );

if( !$oresult ){
	die "Failed to parse program options.";
}

my $narg = @ARGV;
if ( $narg < 1 or $narg > 2 or $help > 0 ){
	print "$0 <input file> [2nd input file]  
	[-h print out this help message] 
	[-warn print out warnings] 
	[-maxid i]
	[-id_var_name id variable name (default=VisitNumber)] 
	[-ofile output file name] 
	[-sv study variable (default=Upc). If set to ALL, then every variable will be counted.]
	[-counter counter variable]
	[-chop_max Set the maximum idf to zero.]
	[-double_crossed Add to pair of variables to double cross.]
	[-count_two insure that the variable appears in two files before giving it any weight (obviously only works for two input files)]
	[-idf the inverse document frequency function to use (default=0)]
	idf:
		0 : 1 / raw frequency of term in file (this is NOT the idf)
		1 : N / event-freq, Number of events N divided by number of events term appears. 
		2 : log( N / event-freq )
		3 : event-freq
	[-vfile : The variable file contains a list of variable names. Useful when there are too many to list on command line.]\n"; 
	exit;
}

#if( !defined( $tvn ) ){
#	print "Please define target variable name (-tvn name)\n";
#	exit;
#}

my @files = @ARGV;
my $nfiles = @files;
my %null;
my %freq;
my %exists;
my %vocab;
my $oldid;
my $id;
my $ndoc=0;
my %step2list;
my %step3list;
my ($c, $v, $C, $V, $mgr0, $meq1, $mgr1, $_v);

sub f0 {
	($_) = @_;
	return 1 / $_;
}
sub f1 {
	($_) = @_;
	return $ndoc / $_;
}
sub f2 {
	($_) = @_;
	return log( $ndoc / $_ );
}
sub f3 {
	($_) = @_;
	return $_;
}
my $csv = Text::CSV_XS->new ({ binary => 1 });
my %weight;
if( defined( $weight_file ) ){
	open( my $wfp, $weight_file ) or die "Could not open idf weight file: $weight_file";
	my $nl=0;
	while (my $row = $csv->getline ($wfp)) {
		if(!( $$row[0] =~ /^\#/) and $$row[1] =~ /^\d+$/ ){
			my $ncol = @$row;
			$ncol == 2 or die "Number of columns ($ncol) in frequency file not two: $weight_file";
			my $val = $$row[0];
			my $w = $$row[1]; 
			if( $weight_function == 0 ){
				$w = $w;
			}
			elsif( $weight_function == 1 ){
				$w = 1/$w;
			}
			elsif( $weight_function == 2 ){
				$w = 1+ log( $w );
			}
			elsif( $weight_function == 3 ){
				$w = 1 / ( 1 + log( $w ));
			}
			else{
				die "Unknown IDF weight function id: $weight_function";
			}
			$weight{$val} = $w;
		}
		$nl++;
	}
	close($wfp);
	$debug and print "Read $nl lines of data from IDF weight file $weight_file\n";
}
my @idf_function = ( \&f0, \&f1, \&f2, \&f3 );
my $idff;
if( $idf >= 0 and $idf <= 3 ){
	$idff = $idf_function[$idf];
}
else{
	die "Unknown idf option: $idf";
}
$debug and print "Use Idf function \# $idf\n";
my %vartype;
my %varbin;
if( defined( $vfile ) ){
	open my $vfp, $vfile or die "Could not open $vfile: $!";
	while( my $lr = $csv->getline($vfp) ){
		my $var = $$lr[0];
		my $vartype = $$lr[1];
		#push @sv, $var;
		$vartype{$var} = $vartype;
		if( $vartype eq "CONTINUOUS" or $vartype eq "DISCRETE" ){
			if( $$lr[2] eq "BIN" ){
				$varbin{$var} = $$lr[3];
			}
		}
	}
	#$nsv = @sv;
	close( $vfp );
	$debug and print "Will bin data as indicated in $vfile\n";
}
my %stemmed;
if( $use_stemmer ){
	initialise_stemmer();
}
my $ifn = 0;
foreach my $ifile (@files){
	open my $io, "<", $ifile or die "Could not open $ifile: $!";
	my $header_ref; 
	do{
		$header_ref = $csv->getline ($io); # search for header
	}
	until( !( $$header_ref[0] =~ /^#/ ));
	$debug and print "Reading file $ifile\n";
	my @key = @$header_ref;    # get keys from header and parse
	my $nkeys = @key;
	my @svars;
	my @isvars; 
	$debug and print "Found $nkeys header keys\n";
	my %varno;
	for( my $i = 0; $i < $nkeys; $i++ ){
		$varno{$key[$i]} = $i;             # key to variable number map. : variable name -> number
		if( $xsv eq "ALL" and $key[$i] ne $id_var_name and $key[$i] ne $tvn ){
			push @svars, $key[$i];
			push @isvars, $i;
			$debug and print "$i\t$key[$i]\n";
		}
	}
	my $no_double_crossed = @double_crossed;
	my $v1;
	my $v2;
	my $sv;
	if( $no_double_crossed == 2 ){
		($v1, $v2) = @double_crossed;
		if( defined( $varno{$v1} ) and defined( $varno{$v2} ) ){
			$sv = $v1 . ":X:" . $v2;
		}
		else{
			die "Unknown variables to double cross: $v1 and/or $v2";
		}
		$debug and print "Study variable: $sv\n";
	}
	elsif( $no_double_crossed != 0 ){
		die "Cant cross: @double_crossed";
	}
	elsif( $xsv eq "ALL" ){
		$debug and  print "Will Count the frequency of all variables\n";
	}
	elsif( !defined( $varno{$xsv} ) ){
		die "Unknown study variable: $xsv";
	}
	else{
		$debug and print "Study variable: $xsv\n";
		$sv = $xsv;
	}

	if( defined( $varno{$id_var_name} ) ){
		$id_var_no = $varno{$id_var_name};
	}
	else{
		die "Unknown ID variable: $id_var_name";
	}
	$debug and print "Id variable number : $id_var_no\n";
	if( defined( $counter ) ){
		if( defined( $varno{$counter} ) ){
			$debug and print "Utilize counter variable: $counter\n";
		}
		else{
			die "Unknown counter variable: $counter";
		}
	}
	my $lineno = 0;
	while (my $row = $csv->getline ($io)) {
		if( $$row[0] !~ /\#/ and $$row[$id_var_no] =~ /^[0-9]+$/ ){
			$id = $$row[$id_var_no];
			my $val;
			if( $lineno++ == 0 ){
				$oldid = $id;
			}
			if( $id != $oldid ){
				process_event($ifn);
			}
			if( $no_double_crossed == 2 ){
				$val = $$row[$varno{$v1}] . ":x:" . $$row[$varno{$v2}];
				if( defined( $exists{$sv}{$val} ) ){
					$exists{$sv}{$val}++;
				}
				else{
					$exists{$sv}{$val} = 1;
				}
			}
			elsif( $xsv eq "ALL" ){
				foreach $sv (@svars){ 
					$val = $$row[$varno{$sv}];
					$val = ( defined( $varbin{$sv} ) and $val =~ /^[0-9.]+$/ ) ? 
						int( $val / $varbin{$sv} ) : 
						$val; 
					if( defined( $exists{$sv}{$val} ) ){
						$exists{$sv}{$val}++;
					}
					else{
						$exists{$sv}{$val} = 1;
					}
					if( defined( $counter ) ){ # the only purpose here is to add negative keywords to vocabulary
						my $cnt = $$row[$varno{$counter}];
						if( $cnt < 0 ){
							$val = "-" . $val;
							if( defined( $exists{$sv}{$val} ) ){
								$exists{$sv}{$val}++;
							}
							else{
								$exists{$sv}{$val} = 1;
							}
						}
					}
				}
			}
			elsif( $use_stemmer ){
				$val = $$row[$varno{$sv}];
				my $w =  defined( $weight_file ) ? ( defined( $weight{$val} ) ? $weight{$val} : 1 ) : 1;
				my @vals = split/[\s\,]+/, $val;
				foreach $val (@vals){
					$val = lc( $val );
					$val =~ s/[\(\)\[\]]//g;
					if( !defined( $stemmed{$val} ) ){
						$val = $stemmed{$val} = stem($val); 
					}
					else{
						$val = $stemmed{$val};
					}
					if( defined( $exists{$sv}{$val} ) ){
						$exists{$sv}{$val} += $w;
					}
					else{
						$exists{$sv}{$val} = $w;
					}
					if( defined( $counter ) ){ # the only purpose here is to add negative keywords to vocabulary
						my $cnt = $$row[$varno{$counter}];
						if( $cnt < 0 ){
							$val = "-" . $val;
							if( defined( $exists{$sv}{$val} ) ){
								$exists{$sv}{$val} += $w;
							}
							else{
								$exists{$sv}{$val} = $w;
							}
						}
					}
				}
			}
			else{
				$val = $$row[$varno{$sv}];
				$val = ( defined( $varbin{$sv} ) and $val =~ /^[0-9.]+$/ ) ? 
				int( $val / $varbin{$sv} ) : $val; 
				if( defined( $exists{$sv}{$val} ) ){
					$exists{$sv}{$val}++;
				}
				else{
					$exists{$sv}{$val} = 1;
				}
				if( defined( $counter ) ){ # the only purpose here is to add negative keywords to vocabulary
					my $cnt = $$row[$varno{$counter}];
					if( $cnt < 0 ){
						$val = "-" . $val;
						if( defined( $exists{$sv}{$val} ) ){
							$exists{$sv}{$val}++;
						}
						else{
							$exists{$sv}{$val} = 1;
						}
					}
				}
			}
		}
	}
	if( defined( $ofile ) ){
		close($io);
	}
	$ifn++;
}

sub process_event{
	my ($ifn) = @_;
	$ndoc++;
	foreach my $sv (keys %exists){
		foreach my $val (keys %{ $exists{$sv} } ){
			if( $idf == 0 ){ # this calculates the term frequency in all documents.
				if( defined( $freq{$ifn}{$sv}{$val} ) ){
					$freq{$ifn}{$sv}{$val} += $exists{$sv}{$val};
				}
				else{
					$freq{$ifn}{$sv}{$val} = $exists{$sv}{$val};
				}
			}
			elsif( defined( $freq{$ifn}{$sv}{$val} ) ) { # calculates frequency of documents containing term.
				$freq{$ifn}{$sv}{$val}++;
			}
			else{
				$freq{$ifn}{$sv}{$val} = 1;
			}
			$vocab{$sv}{$val} = 1;
		}
	}
	%exists = %null;
	$oldid = $id;
}

$debug and print "Done collecting data, now sort and print.\n";
my $ofp;
if( defined( $ofile ) ){
	open( $ofp, ">$ofile" ) or die "Could not open $ofile";
}
else{
	$ofp = *STDOUT;
}
my $date = `date "+%F (%A) %T %Z"`;
chomp $date;
print $ofp "# $date : $arguments\n";
unless ($noheader) {
	if( $xsv ne "ALL" ){
		print $ofp "$xsv,idf\n";
	}
	elsif( $nfiles == 2 ){
		print $ofp "var,val,idf1,idf2\n";
	}
	else{
		print $ofp "var,val,idf\n";
	}
};
my @vars = sort var_sort_func (keys %vocab);
my $nvars = @vars;
my $maxval = 0;
#if( 0 ){
##	if( $chop_max > 0 ){
#		my $maxkey = $keys[$nvars-1];
#		my $fmax = $freq{$maxkey};
#		if( $idf == 0 ){
#			$maxval = 1/$fmax; 
#		}
#		elsif( $idf == 1 ){
#			$maxval = $ndoc/$fmax;
#		}
#		elsif( $idf == 2 ){
#			$maxval = log( $ndoc / $fmax );
#		}
#	}
#	else{
#		$maxval = 0;;
#	}
#}
my $gvar;
my %s1;
my %s2;
sub freq_sort_func{
	if( defined(  $s1{$b} ) ){
		if( defined( $s1{$a} ) ){
			return $s1{$b} <=> $s1{$a};
		}
		return $s1{$b} <=> $s2{$a};
	}
	elsif( defined( $s1{$a} ) ){
		return $s2{$b} <=> $s1{$a};
	}
	return $s2{$b} <=> $s2{$a};
}

foreach $gvar (@vars){
	%s1 = %{ $freq{0}{$gvar} };
	if( defined( $freq{1}{$gvar} ) ){
		%s2 = %{ $freq{1}{$gvar} };
	}
	foreach my $val (sort freq_sort_func keys %{ $vocab{$gvar} }){
		if( $nfiles == 1 ){
			my $f = &$idff( $s1{$val} );
			my $pl =  $novarprint ? "\"$val\",$f\n" : "\"$gvar\",\"$val\",$f\n";
			print $ofp $pl; 
		}
		else{
			my $f1 = 0;
			my $f2 = 0;
			if( defined( $s1{$val} ) ){
				$f1 = &$idff(  $s1{$val} );
			}
			if(  defined( $s2{$val} ) ){
				$f2 = &$idff(  $s2{$val} );
			}
			if( $count_two  ){
				if( $f1 > 0 and $f2 > 0 ){
					print $ofp "\"$gvar\",\"$val\",$f1,$f2\n";
				}
			}
			else{
				print $ofp "\"$gvar\",\"$val\",$f1,$f2\n";
			}
		}
	}
}
if( defined( $ofile ) ){
	close( $ofp );
}
sub var_sort_func{
	if( $a =~ /[^0-9.]+/ or $b =~ /[^0-9.]+/ ){
		return $a cmp $b;
	}
	return $a <=> $b;
}


if( defined( $ofile ) ){
	print "New IDF file: $ofile\n";
}

# Porter stemmer in Perl. Few comments, but it's easy to follow against the rules in the original
# paper, in
#
#   Porter, 1980, An algorithm for suffix stripping, Program, Vol. 14,
#   no. 3, pp 130-137,
#
# see also http://www.tartarus.org/~martin/PorterStemmer

# Release 1


sub stem
{  my ($stem, $suffix, $firstch);
	my $w = shift;
	if (length($w) < 3) { return $w; } # length at least 3
	# now map initial y to Y so that the patterns never treat it as vowel:
	$w =~ /^./; $firstch = $&;
	if ($firstch =~ /^y/) { $w = ucfirst $w; }

	# Step 1a
	if ($w =~ /(ss|i)es$/) { $w=$`.$1; }
	elsif ($w =~ /([^s])s$/) { $w=$`.$1; }
	# Step 1b
	if ($w =~ /eed$/) { if ($` =~ /$mgr0/o) { chop($w); } }
	elsif ($w =~ /(ed|ing)$/)
	{  $stem = $`;
		if ($stem =~ /$_v/o)
		{  $w = $stem;
			if ($w =~ /(at|bl|iz)$/) { $w .= "e"; }
			elsif ($w =~ /([^aeiouylsz])\1$/) { chop($w); }
			elsif ($w =~ /^${C}${v}[^aeiouwxy]$/o) { $w .= "e"; }
		}
	}
	# Step 1c
	if ($w =~ /y$/) { $stem = $`; if ($stem =~ /$_v/o) { $w = $stem."i"; } }

	# Step 2
	if ($w =~ /(ational|tional|enci|anci|izer|bli|alli|entli|eli|ousli|ization|ation|ator|alism|iveness|fulness|ousness|aliti|iviti|biliti|logi)$/)
	{ $stem = $`; $suffix = $1;
		if ($stem =~ /$mgr0/o) { $w = $stem . $step2list{$suffix}; }
	}

	# Step 3

	if ($w =~ /(icate|ative|alize|iciti|ical|ful|ness)$/)
	{ $stem = $`; $suffix = $1;
		if ($stem =~ /$mgr0/o) { $w = $stem . $step3list{$suffix}; }
	}

	# Step 4

	if ($w =~ /(al|ance|ence|er|ic|able|ible|ant|ement|ment|ent|ou|ism|ate|iti|ous|ive|ize)$/)
	{ $stem = $`; if ($stem =~ /$mgr1/o) { $w = $stem; } }
	elsif ($w =~ /(s|t)(ion)$/)
	{ $stem = $` . $1; if ($stem =~ /$mgr1/o) { $w = $stem; } }


	#  Step 5

	if ($w =~ /e$/)
	{ $stem = $`;
		if ($stem =~ /$mgr1/o or
			($stem =~ /$meq1/o and not $stem =~ /^${C}${v}[^aeiouwxy]$/o))
		{ $w = $stem; }
	}
	if ($w =~ /ll$/ and $w =~ /$mgr1/o) { chop($w); }

	# and turn initial Y back to y
	if ($firstch =~ /^y/) { $w = lcfirst $w; }
	return $w;
}

sub initialise_stemmer {

	%step2list =
	( 'ational'=>'ate', 'tional'=>'tion', 'enci'=>'ence', 'anci'=>'ance', 'izer'=>'ize', 'bli'=>'ble',
		'alli'=>'al', 'entli'=>'ent', 'eli'=>'e', 'ousli'=>'ous', 'ization'=>'ize', 'ation'=>'ate',
		'ator'=>'ate', 'alism'=>'al', 'iveness'=>'ive', 'fulness'=>'ful', 'ousness'=>'ous', 'aliti'=>'al',
		'iviti'=>'ive', 'biliti'=>'ble', 'logi'=>'log');

	%step3list =
	('icate'=>'ic', 'ative'=>'', 'alize'=>'al', 'iciti'=>'ic', 'ical'=>'ic', 'ful'=>'', 'ness'=>'');


	$c =    "[^aeiou]";          # consonant
	$v =    "[aeiouy]";          # vowel
	$C =    "${c}[^aeiouy]*";    # consonant sequence
	$V =    "${v}[aeiou]*";      # vowel sequence

	$mgr0 = "^(${C})?${V}${C}";               # [C]VC... is m>0
	$meq1 = "^(${C})?${V}${C}(${V})?" . '$';  # [C]VC[V] is m=1
	$mgr1 = "^(${C})?${V}${C}${V}${C}";       # [C]VCVC... is m>1
	$_v   = "^(${C})?${v}";                   # vowel in stem

}

# that's the definition. Run initialise() to set things up, then stem($word) to stem $word, as here:


#initialise();
#
#while (<>)
#{
#	{  /^([^a-zA-Z]*)(.*)/ ;
#		print $1;
#		$_ = $2;
#		unless ( /^([a-zA-Z]+)(.*)/ ) { last; }
#		$word = lc $1; # turn to lower case before calling:
#		$_ = $2;
#		$word = stem($word);
#		print $word;
#		redo;
#	}
#	print "\n";
#}

# inputs taken from the files on the arg list, output to stdout.

# As an easy speed-up, one might create a hash of word=>stemmed form, and look up each new
# word in the hash, only calling stem() if the word was not found there.
;
