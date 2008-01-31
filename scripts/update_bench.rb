#!/usr/bin/ruby
require "timeout"

# trier_res = "/home/vesal/kool/magister/projects/results_rtmm/"
goblint = File.join(Dir.getwd,"goblint")
fail "Please run script from goblint dir!" unless File.exist?(goblint)
testresults = File.expand_path("tests/bench_result") + "/"
bench = "../bench/"

class Project
  attr_reader :name, :group, :path, :params
  def initialize(name, size, desc, group, path, params)
    @name     = name
    @size     = size
    @desc     = desc
    @group    = group
    @path     = path
    @params   = params
  end
  def to_html
    "<td>#{@name}</td>\n" + "<td>#{@desc}</td>\n" + "<td>#{@size}</td>\n"
  end
  def to_s
    "#{@name} -- #{@desc}"
  end
end


#Command line parameters

timeout = 300
timeout = ARGV[0].to_i unless ARGV[0].nil?
only = ARGV[1] unless ARGV[1].nil?
# analyses = ["mutex", "base", "cpa", "intcpa"]
# analyses = ["mutex", "no_path"]
analyses = ["mutex"]

#processing the input file

projects = []
File.open("tests/projects.txt", "r") do |f|
  i = 0
  while line = f.gets
    next if line =~ /^\s*$/ 
    if line =~ /Group: (.*)/
      gname = $1
      next
    end
    name = line.chomp
    description = f.gets.chomp
    path = File.expand_path(f.gets.chomp, bench)
    size = `wc -l #{path}`.split[0] + " lines"
    params = f.gets.chomp
    params = "" if params == "-"
    p = Project.new(name,size,description,gname,path,params)
    projects << p
  end
end

#analysing the files
gname = ""
projects.each do |p|
  next unless only.nil? or p.name == only 
  if p.group != gname then
    gname = p.group
    puts gname
  end
  filepath = p.path
  dirname = File.dirname(filepath)
  filename = File.basename(filepath)
  Dir.chdir(dirname)
  puts "Analysing #{filename}"
  analyses.each do |a|
    puts "  " + a
    outfile = testresults + File.basename(filename,".c") + ".#{a}.txt"
    `timeout #{timeout} #{goblint} #{filename} #{p.params} --analysis #{a} --stats 1>#{outfile} 2>&1`
    if $? != 0 then
      puts "  Timed out! (or other failure)"
      `echo "TIMEOUT                    #{timeout} s" >> #{outfile}`
    end
  end
end

File.open(testresults + "index.html", "w") do |f|
  f.puts "<html>"
  f.puts "<head><title>Test Results</title></head>"
  f.puts "<body>"
  f.puts "<table border=2 cellpadding=4>"
  gname = ""
  projects.each do |p|
    if p.group != gname then
      gname = p.group
      f.puts "<tr><th colspan=#{3+2*analyses.size}>#{gname}</th></tr>"
      f.puts "<tr><th>Name</th><th>Description</th><th>Size (merged)</th>"
      analyses.each do |a| 
        f.puts "<th>#{a}</th>"
        f.puts "<th>warnings</th>"
      end
#       f.puts "<th>Compared to Trier</th>"
    end
    f.puts "<tr>"
    f.puts p.to_html
    analyses.each do |a|
      outfile = File.basename(p.path,".c") + ".#{a}.txt"
      File.open(testresults + outfile, "r") do |g|
        lines = g.readlines
        warnings = lines.grep(/Datarace over variable/).size
        res = lines.grep(/^TOTAL\s*(.*) s.*$/) { |x| $1 }
        if res == [] then
          res = lines.grep(/^TIMEOUT\s*(.*) s.*$/) { |x| $1 }
          if res == [] then
            f.puts "<td><a href = #{outfile}>failed</a></td>"
          else
            f.puts "<td><a href=\"#{outfile}\">#{res.to_s} s</a> (limit)</td>"
          end
        else
          f.puts "<td><a href = #{outfile}>#{res.to_s} s</a></td>"
        end
        f.puts "<td>#{warnings} races</rd"
      end
    end
    gb_file = testresults + File.basename(p.path,".c") + ".mutex.txt"
#     tr_file = trier_res + p.name + "/warnings.txt"
#     if FileTest.exists? tr_file then
#       comp_file = File.basename(p.path,".c") + ".comparison.txt" 
#       `/home/vesal/kool/magister/goblint/scripts/mit_Trier_vergleichen.rb #{gb_file} #{tr_file} > #{testresults + comp_file}`
#       summary = File.new(testresults + comp_file).readlines[-1]
#       f.puts "<td><a href=\"#{comp_file}\">#{summary}</td>"
#     else
#       f.puts "<td>No Trier!</td>"
#     end
    f.puts "</tr>"
    f.puts "</tr>"
  end
  f.puts "</table>"
  f.puts "</body>"
  f.puts "</html>"
end