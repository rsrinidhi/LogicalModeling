import java.util.*;

import lpsolve.*;

import java.io.*;


/*The system is designed for a generic pathway
 * b matrix is 2D of size n*n. It is dependency matrix
 * x1 matrix is constructed based on the interactions and the nodes are activated in the sequence
 * x matrix is assigned based on a random row that is generated.
 * y matrix is the one on which the constraints are imposed. The size of the matrix is n*n.It is 1D array
 * Once the constraints are implemented,the matrix is converted into a 2D array, nmatrix
 * The rows of nmatrix are checked with x1 matrix to check if atleast one row matches if not exactly, but still satisfy 
 * most of the cases
 * If it matches,then it is checked with x1 matrix for the most number of similarities and the states are assigned
 * EGFR:csrc
 * IL1:mtorc2
 * IL6:mtor
 * MAPK:DISPATCHED
 */

public class Vertices {

	int number,state,expstate,newstate=0,count=0;
	String name;
	//arraylist to maintain the parents of the nodes
	ArrayList<Vertices> parent= new ArrayList<Vertices>();

	public Vertices(int n)
	{
		number=n;
	}


	public static void main(String args[])throws LpSolveException
	{
		Scanner sc= new Scanner(System.in);
		String pathway= new String();
		
		

		System.out.println("______________________________________________________________________________");
		System.out.println("                Signaling pathways");
		System.out.println("1.EGFR signaling pathway");
		System.out.println("2.IL1 signaling pathway");
		System.out.println("3.IL6 signaling pathway");
		System.out.println("4.MAPK signaling pathway");
		System.out.println("5.Exit");
		System.out.println("______________________________________________________________________________");
		System.out.print("Please enter your choice: ");
		int input= sc.nextInt();
		System.out.println();

		while(input==1|| input==2||input==3||input==4)
		{

			if(input==1)
				pathway="EGFR";
			else if(input==2)
				pathway="IL1";
			else if(input==3)
				pathway="IL6";
			else if(input==4)
				pathway="MAPK";
			else
				System.out.println("Invalid Input!!Please Enter again.");

				
			int k=0;
			double sum=0,tmp=0;
			Vertices[] vs = new Vertices[200];

			for(int i=0;i<200;i++)
				vs[i]= new Vertices(i);

			//initialize the nodes
			int n=initialize(vs,pathway);
			//Initialize the input nodes
			String[] Nodes=initializeNode(vs,n,pathway);
			//initialize the states
			int number=initializeState(vs,n,pathway);
			//dependency matrix based on activation and repression
			int[][] b= new int[n][n];
			//selecting a row of the truth table
			int[] x= new int[n];	
			//variable to store the number of parents
			int nr=initializeParents(vs,n,pathway);
			int no= n*nr*10;
			double[][] x1= new double[nr+1][n];
			double[] y= new double[no];
			double[] newmatrix= new double[no];
			//Computing the states of the intermediate nodes
			computeStates(vs,Nodes,n,number,pathway);
			//removing the duplicates if any such parent exists
			removeDuplicates(vs,n);
			initialiseBMatrix(b,n,pathway,vs);
			initialiaseXMatrix(x1,y,vs,n,nr,pathway);
			//Generate a row randomly from the table
			int randomNum = 0 + (int)(Math.random()*n); 

			for(int i=0;i<n;i++)
			{	for(int j=0;j<nr;j++)
				if(j==randomNum)
					x[i]=(int)x1[randomNum][i];
			}

			LpSolve problem = LpSolve.makeLp(n, n);
			problem.setLpName("Reconstructing Boolean Models of Signaling");

			for(int i=1;i<n;i++)
			{
				problem.setBounds(i, 0, 1);
				problem.setBinary(i,true);
			}

			k=0;
			for(int i=0;i<nr;i++)
				for(int j=0;j<n;j++)
					y[k++]=x1[i][j];

			newmatrix=y;



			//constraint 1
			//y(v,i)<= x(v,i) 
			problem.addConstraint(newmatrix,LpSolve.LE,0);

			//constraint 2
			//y(v,i)<= (1-b[i][j])+ a(u(vj))*[2b[i][j]-1]
			k=0;
			for(int i=0;i<n;i++)
			{
				for(int j=0;j<n;j++)
				{
					k++;
					for(int p=0;p<number;p++)
					{
						if(Nodes[p].equals(vs[j].name))
						{
							y[k]+=(vs[j].state* (2*b[i][j]-1) -b[i][j]);
							newmatrix[k]+=(vs[j].state* (2*b[i][j]-1) -b[i][j]);
						}		
					}
				}
			}

			problem.addConstraint(newmatrix,LpSolve.LE,1);

			//constraint 3
			//y(vi)>=x(vi)+ sigma(j)[2b(v,i,j)a(u(vj)) - a(u(vj)-b(v,i,j)]

			for(int i=0;i<n;i++)
			{
				for(int j=0;j<n;j++)
				{
					sum=0;
					for(int p=0;p<number;p++)
						if(Nodes[p].equals(vs[j].name))
						{
							sum+= 2*b[i][j]*vs[j].state - vs[j].state - b[i][j];
						}
				}	
			}

			for(int i=0;i<n;i++)
			{
				y[i]=x[i]+sum;
				newmatrix[i]=(double)x[i];
			}

			problem.addConstraint(newmatrix, LpSolve.GE, sum);

			//constraint 4
			//y(vi)<=a(vi)<=1
			double[] newtemp= new double[n];
			for(int i=0;i< n;i++)
			{
				newtemp[i]=vs[i].state;
				newmatrix[i]=1-newtemp[i];
				y[i]=1-newtemp[i];		
			}


			problem.addConstraint(newmatrix,LpSolve.LE, 1);


			//constraint 5
			//a(v)<=sigma i y(vi)		
			sum=0;
			for(int i=0;i<n;i++)
			{
				sum+= y[i];
			}	 
			problem.addConstraint(newtemp,LpSolve.LE,sum);

			//constraint 6 & 7
			//a(V)>=(sigma j a(u(v)j)-x(v) +1)/(n+1)
			//a(V)<=(sigma j a(u(v)j)-x(v))/(n+1)+1	 
			sum=0;
			int[] sum1= new int[n];
			int[] sum2= new int[n];
			for(int i=0;i<number;i++)
			{
				for(int j=0;j<n;j++)
				{
					if(vs[j].name.equals(Nodes[i]))
					{
						sum+=vs[j].state;
					}
				}
			}


			for(int i=0;i<n;i++)
			{
				sum1[i] = (int)(x[i]-1-sum)/(n+1);
				sum2[i] = (int)((x[i]-sum)/(n+1))+1;
			}

			for(int i=0;i<n;i++)
			{				
				problem.addConstraintex(i,newtemp,sum1,LpSolve.GE,0);
				problem.addConstraintex(i,newtemp,sum2,LpSolve.LE,0);
			}



			//Objective Function
			//sigma (state of the nodes) - (state of the node) * (experimental state of the node)
			sum=0;tmp=0;
			for(int i=0;i<n;i++)
			{
				sum+=vs[i].state; 
			}
			for(int i=0;i<n;i++)
			{
				tmp= sum - vs[i].state * vs[i].expstate;
				problem.setObj(i, tmp);
			}


			problem.setVerbose(1);
			problem.solve(); 
			double[] Y= problem.getPtrVariables();
			Y=y;
			

			k=0;
			double[][] nmatrix= new double[nr][n];
			for(int i=0;i<nr;i++)
				for(int j=0;j<n;j++)
				{if(y[k]<0)
					nmatrix[i][j]=y[k++] *-1;
				else
					nmatrix[i][j]=y[k++];}

			double countercompare=Compare(x1,nmatrix,n,nr,vs)[0];	
			double percentage=Compare(x1,nmatrix,n,nr,vs)[1];

			if(countercompare>0)
				printOutput(vs,n,pathway,percentage,Nodes);
			else
				System.out.println("Yaay!! No output node is activated.");


			if(problem.getLp() != 0)
				problem.deleteLp();

			System.out.print("\nPlease enter your choice : ");
			input= sc.nextInt();
			System.out.println();


		}
	}

	/*Initializing all the nodes from the file nodes.txt. This is the data set obtained from 
the CellNetAnalyzer repository */
	public static int initialize(Vertices[] vs,String pathway)
	{
		int ct=0;
		for(int i=0;i<200;i++)
			vs[i]= new Vertices(i);
		try
		{
			String path1 = new String("./FYP/");
			String path2 = new String("/nodes.txt");
			String path3 = path1.concat(pathway);
			String path4 = path3.concat(path2);

			FileInputStream fstream = new FileInputStream(path4);
			BufferedReader br = new BufferedReader(new InputStreamReader(fstream));
			String strLine;
			String[] str= new String[2];
			while ((strLine = br.readLine()) != null) 	
			{ 
				int j=0;
				StringTokenizer st = new StringTokenizer(strLine,":");
				while (st.hasMoreElements()) 
				{
					str[j++]=(String) st.nextElement();
				}

				vs[ct].name=str[0];
				vs[ct].expstate= Integer.parseInt(str[1]);
				vs[ct].state=0;
				vs[ct].number=ct+1;
				ct++;
			}
			fstream.close();
		}

		catch (Exception e)
		{
			System.err.println("Error " + e.getMessage());
		}
		return ct;

	}

	/*initializing the states of the input nodes from the dataset*/
	public static int initializeState(Vertices[] vs,int n,String pathway)
	{ 	
		Scanner sc = new Scanner(System.in);
		int ct=0,flag=0;
		try
		{
			String node= new String();
			String[] str= new String[2];
			String path1 = new String("/FYP/");
			String path2 = new String("/States.txt");
			String path3 = path1.concat(pathway);
			String path4 = path3.concat(path2);
			char input;

			FileInputStream fstream = new FileInputStream(path4);
			BufferedReader br = new BufferedReader(new InputStreamReader(fstream));
			String strLine;
			while ((strLine = br.readLine()) != null) 	
			{
				int i=0;
				StringTokenizer st = new StringTokenizer(strLine,":");
				while (st.hasMoreElements()) 
				{
					str[i++]=(String) st.nextElement();
				}
				for(int j=0;j<n;j++)
				{
					if(vs[j].name.equals(str[0]))
					{
						vs[j].state=Integer.parseInt(str[1]);
						ct++;
					}	
				}		
			}

	
			System.out.format("---------------%n");
			
			
			System.out.print("Do you wish to perturb an input node (Y/N)? ");
			input= sc.next().charAt(0);

			while(input=='Y' || input == 'y')
			{
				flag=0;
				System.out.print("Enter the node to be perturbed:");
				node= sc.next();

				for(int i=0;i<n;i++)
				{
					if(vs[i].name.equals(node))
					{
						if(vs[i].state==0)
							vs[i].state=1;
						else
							vs[i].state=0;
						flag++;
					}
				}
				if(flag==0)
					System.out.println("No such node exists!!");

				System.out.print("Do you wish to perturb yet another input node (Y/N)? ");
				input= sc.next().charAt(0);
			}
			
			fstream.close();
		}

		catch (Exception e)
		{
			System.err.println("Error " + e.getMessage());
		}

		return ct;
	}


	public static String[] initializeNode(Vertices[] vs,int n,String pathway)
	{ 	
		String[] Nodes = new String[50];
		int ct=0;
		try
		{

			String[] str= new String[2];
			String path1 = new String("/FYP/");
			String path2 = new String("/States.txt");
			String path3 = path1.concat(pathway);
			String path4 = path3.concat(path2);

			FileInputStream fstream = new FileInputStream(path4);
			BufferedReader br = new BufferedReader(new InputStreamReader(fstream));
			String strLine;
			while ((strLine = br.readLine()) != null) 	
			{
				int i=0;
				StringTokenizer st = new StringTokenizer(strLine,":");
				while (st.hasMoreElements()) 
				{
					str[i++]=(String) st.nextElement();
				}
				for(int j=0;j<n;j++)
				{
					if(vs[j].name.equals(str[0]))
					{
						Nodes[ct++]=vs[j].name;
					}	
				}		
			}
			
			String leftAlignFormat = "| %-10s |%n" ;
			System.out.format("--------------%n");
			System.out.printf("| Input Nodes |%n");
			System.out.format("--------------%n");
			for(int i=0;i<ct;i++)
				System.out.format(leftAlignFormat, Nodes[i]);

			fstream.close();
		}

		catch (Exception e)
		{
			System.err.println("Error " + e.getMessage());
		}

		return Nodes;
	}
	/*The parents of the nodes are added based on the interaction between nodes thereby activating
	 *another node. The interactions are obtained from the dataset as well 
	 */
	public static int initializeParents(Vertices[] vs,int n,String pathway) 
	{
		String s,s1;
		int ct=0;
		try
		{
			String path1 = new String("/FYP/");
			String path2 = new String("/Interactions.txt");
			String path3 = path1.concat(pathway);
			String path4 = path3.concat(path2);

			FileInputStream fstream = new FileInputStream(path4);
			BufferedReader br = new BufferedReader(new InputStreamReader(fstream));
			String strLine;

			while ((strLine = br.readLine()) != null) 	
			{	
				StringTokenizer st = new StringTokenizer(strLine, " +!=");
				ArrayList<String> str= new ArrayList<String>();
				while (st.hasMoreElements()) 
				{
					str.add((String) st.nextElement());
				}
				s=str.get(str.size()-1).toString();
				for(int i=0;i<n;i++)
				{
					s1=vs[i].name.toString();

					if(s1.equalsIgnoreCase(s))
					{
						for(int j=0;j<str.size()-1; j++)
						{
							for(int k=0;k<n;k++)
							{	
								if(vs[k].name.equals(str.get(j)))
									vs[i].parent.add(vs[k]);
							}
						}
					}
				}
				ct++;
			}

			fstream.close();
		}

		catch (Exception e)
		{
			System.err.println("Error " + e.getMessage());
		}
		return ct;
	}

	/*
	 *While adding the parents, it is possible that a node is added multiple number of times.
	 *Therefore this function removes the duplicate nodes. 
	 */
	public static void removeDuplicates(Vertices[] vs, int n)
	{
		for(int i=0;i<n;i++)
		{
			vs[i].parent = new ArrayList<Vertices>(new LinkedHashSet<Vertices>(vs[i].parent));			
		}
	}

	/*
	 * The state of the intermediary nodes are computed based on the state of the input nodes
	 * and the interaction between the nodes
	 */
	public static void computeStates(Vertices[] vs,String[] Nodes,int n,int number,String pathway)
	{
		try
		{
			String[] str= new String[3];

			String path1 = new String("./FYP/");
			String path2 = new String("/Interactions.txt");
			String path3 = path1.concat(pathway);
			String path4 = path3.concat(path2);

			FileInputStream fstream = new FileInputStream(path4);
			BufferedReader br = new BufferedReader(new InputStreamReader(fstream));
			String strLine;

			int test2=0;
			while ((strLine = br.readLine())!= null) 	
			{
				int i=0,p=0,counter=0,test=0;
				test2++;
				ArrayList<String> newstring= new ArrayList<String>();
				StringTokenizer st = new StringTokenizer(strLine,"=");
				while (st.hasMoreElements()) 
				{
					str[i++]=(String) st.nextElement();
				}

				StringTokenizer st1 = new StringTokenizer(str[0],"+");
				while (st1.hasMoreElements()) 
				{
					newstring.add((String) st1.nextElement());
				}

				for(int j=0;j<newstring.size();j++)
				{	
					for(int k=0;k<number;k++)
					{
						if(newstring.get(j).equals(Nodes[k]))
						{
							for(int l=0;l<n;l++)
								if(vs[l].name.equals(newstring.get(j)))
								{
									test++;
									newstring.set(j,"null");
									if(vs[l].state==vs[l].expstate)
										p++;
								}
						}
					}
					if(newstring.get(j).substring(0,1).equals("!"))
					{
						for(int r=0;r<n;r++)
							if(newstring.get(j).substring(1).equals(vs[r].name))
							{
								test++;
								if(vs[r].state == vs[r].expstate)
									counter++;
							}
					}
					else
					{
						for(int s=0;s<n;s++)
							if(newstring.get(j).equals(vs[s].name))
							{	
								test++;
								if(vs[s].count==0 || vs[s].state==vs[s].expstate)
									p++;
							}
					}
				}

				for(int j=0;j<n;j++)			
				{
					if(vs[j].name.equals(str[1]))
					{
						test++;
						if(p==(newstring.size()-counter))
							vs[j].state=vs[j].expstate;
						else
						{
							vs[j].count++;
							if(vs[j].expstate==0)
								vs[j].state=1;
							else
								vs[j].state=0;
						}					
					}
				}	

				if(test!=newstring.size()+1)
					System.out.println(test2 + " I am special "+ test + "  " + newstring.size()) ;
			}		
			fstream.close();
		}

		catch (Exception e)
		{
			System.err.println("Error " + e.getMessage());
		}
	}
	/*
	 * The b[][] is a two dimensional dependency matrix that is obtained from the paper
	 * Logic of IL1 signaling pathways
	 */
	public static void initialiseBMatrix(int[][]b,int n,String pathway,Vertices[] vs)
	{
		/*if(pathway.equals("EGFR"))
		{
			for(int i=0;i<n;i++)
			{	
				if(i==0||i==1||i==2||i==3||i==9||i==10||i==11||i==12||i==13||i==14||i==16||i==18||i==33||i==34||i==35||i==36||i==37||i==38||i==39||i==40||i==41||i==42||i==43||i==44||i==45||i==46||i==47||i==48||i==49||i==50||i==51||i==52||i==53||i==54||i==55||i==56||i==64||i==65||i==66||i==67||i==68||i==69||i==70||i==71||i==72||i==73||i==74||i==75||i==76||i==82||i==83||i==84||i==85||i==86||i==87||i==88||i==91||i==93||i==94||i==96||i==97||i==98||i==99||i==101)
					for(int j=0;j<n;j++)
					{
						b[i][j]=0;
						if(i!=j && (j==3 || j==6 || j==7 || j==16 || j==19 || j==20 || j==21 || j==22 || j==23 || j==24 || j==25 ||j==27 ||j==28 ||j==29 ||j==30 ||j==31 ||j==32 ||j==33 ||j==34 ||j==37 ||j==41||j==54 ||j==55 ||j==56 ||j==57 ||j==58 ||j==59 ||j==60 ||j==67 ||j==69 ||j==70 ||j==71 ||j==72||j==80 ||j==82 ||j==86 ||j==94 ||j==92 ||j==93 ||j==98 ||j==100))
						{
							b[i][j]=1;
						}
					}
			}
		}

		else
		{*/
			for(int i=0;i<n;i++)
			{
				for(int j=0;j<n;j++)
				{
					if(i==j)
						b[i][j]=0;
					else
						for(int k=0;k<vs[i].parent.size();k++)
						{
							b[i][vs[i].parent.get(k).number-1]=1;
						}
				}
			}
		}
	//}

	/*
	 *X matrix is a nr*n matrix where nr is the number of interactions and n is the number of nodes
	 *Each interaction is taken as row of the matrix. The species involved in the reaction are 
	 * represented by 1 in the ith row where 0<i<n
	 */
	public static void initialiaseXMatrix(double[][] x1,double[] y,Vertices[] vs,int n,int nr,String pathway)
	{
		try
		{
			String[] str= new String[3];

			String path1 = new String("./FYP/");
			String path2 = new String("/Interactions.txt");
			String path3 = path1.concat(pathway);
			String path4 = path3.concat(path2);

			FileInputStream fstream = new FileInputStream(path4);
			BufferedReader br = new BufferedReader(new InputStreamReader(fstream));
			String strLine;
			int ct=0;
			while ((strLine = br.readLine()) != null) 	
			{				
				int i=0,counter=0;
				ArrayList<String> newstring= new ArrayList<String>();
				StringTokenizer st = new StringTokenizer(strLine,"=");				

				if(ct>=1)
				{
					for(int j=0;j<n;j++)
					{
						if(x1[ct-1][j]==1)
							x1[ct][j]=1;
					}
				}

				while (st.hasMoreElements()) 
				{
					str[i++]=(String) st.nextElement();
				}

				StringTokenizer st1 = new StringTokenizer(str[0],"+");
				while (st1.hasMoreElements()) 
				{
					newstring.add((String) st1.nextElement());
				}

				for(int k=0;k<newstring.size();k++)
				{
					if(newstring.get(k).substring(0,1).equals("!"))
					{
						for(int j=0;j<n;j++)
						{
							if(vs[j].name.equals(newstring.get(k).substring(1)))
							{
								if(vs[j].state==1)
									x1[ct][j]=0;
								else
									x1[ct][j]=1;
							}
						}
					}							
					else
					{
						for(int j=0;j<n;j++)
						{
							if(vs[j].name.equals(newstring.get(k)))
							{
								x1[ct][j]=vs[j].state;
								if(vs[j].state!=vs[j].expstate)
									counter++;
							}
						}
					}
				}

				for(int j=0;j<n;j++)
				{
					if(vs[j].name.equals(str[1]))
					{
						if(counter==0)
						{
							x1[ct+1][j]=1;
						}
					}
				}
				ct++;

				for(int j=0;j<n;j++)
				{
					if(x1[nr-1][j]==1)
						x1[nr][j]=1;
				}
			}

			int k=0;
			for(int i=0;i<nr;i++)
				for(int j=0;j<n;j++)
					y[k++]=x1[i][j];
			fstream.close();
		}

		catch (Exception e)
		{
			System.err.println("Error " + e.getMessage());
		}
	}

	public static double[] Compare(double[][] x1,double[][] nmatrix,int n,int nr,Vertices[] vs)
	{
		int counter=0,p=0;
		double percentage,max=0;
		double[] values= new double[2];
		for(int i=0;i<nr;i++)
		{	
			int ct=0;
			for(int j=0;j<n;j++)
			{	
				if(nmatrix[i][j]==vs[j].state)
					ct++;
			}

			if(i==0){max=ct;p=i;}
			if(ct<=n)
			{	counter++;
			if(ct>max)
			{p=i;max=ct;}}	
		}

		percentage= (double)(max/n)*100;


		for(int i=0;i<n;i++)
		{	
			vs[i].newstate= (int)nmatrix[p][i];
		}

		values[0]=counter;
		values[1]=percentage;
		return values;
	}

	public static void printOutput(Vertices[] vs, int n,String pathway,double percentage,String[] Nodes)
	{
		System.out.println();
		System.out.println("==============================================================================");
		System.out.println("				The " + pathway + " System");
		System.out.println("==============================================================================");
		try
		{
			int ct=0,ct1=0,ct2=0,ct3=0,ct4=0,counter=0;
			String[] output= new String[50];
			int[] states= new int[50];
			char[] flag = new char[50];
			String[] information= new String[50];

			String path1 = new String("./FYP/");
			String path2 = new String("/Output.txt");
			String path3 = path1.concat(pathway);
			String path4 = path3.concat(path2);
			
			
			
			FileInputStream fstream = new FileInputStream(path4);
			BufferedReader br = new BufferedReader(new InputStreamReader(fstream));
			String strLine;
			String[] str= new String[2];
			String leftAlignFormat = "| %-17s | %-9d | %-9d |%n" ;

			System.out.format("--------------------+-----------+-----------+%n");
			System.out.printf("| Output nodes      | State     |Exp.State  |%n");
			System.out.format("--------------------+-----------+-----------+%n");
			while ((strLine = br.readLine()) != null) 	
			{ 
				int j=0;
				StringTokenizer st = new StringTokenizer(strLine,":");
				while (st.hasMoreElements()) 
				{
					str[j++]=(String) st.nextElement();
				}
				for(int i=0;i<n;i++) 
				{
					if(str[0].equals(vs[i].name))
					{
						output[ct]=vs[i].name;
						states[ct]=vs[i].state;
						information[ct]=str[1];

						if(vs[i].state==vs[i].newstate && vs[i].state==vs[i].expstate)
							flag[ct]='Y';
						else
							flag[ct]='N';

						ct++;
						System.out.format(leftAlignFormat, vs[i].name, vs[i].newstate,vs[i].state);
					}

				}
			}

			System.out.format("--------------------+-----------+-----------+%n");
			double newvalue= Math.round(percentage*100)/100d;
			System.out.println("The percentage accuracy of the reconstructed algorithm is "+ newvalue + "%.");
			System.out.println("\n");

			
			for(int i=0;i<ct;i++)
			{
				if(flag[i]=='Y')
					System.out.println(information[i]);
			}

			System.out.println();
			fstream.close();
		}

		catch (Exception e)
		{
			System.err.println("Error " + e.getMessage());
		}
	}
}